// SONIC: Standard library for formally-verifiable distributed contracts
//
// SPDX-License-Identifier: Apache-2.0

use alloc::collections::BTreeSet;
use core::borrow::Borrow;
use std::io;

use amplify::MultiError;
use commit_verify::{ReservedBytes, StrictHash};
use indexmap::IndexSet;
use sonic_callreq::MethodName;
use sonicapi::{Api, NamedState, OpBuilder, SemanticError, Semantics, SigBlob};
use strict_encoding::{
    DecodeError, ReadRaw, SerializeError, StrictDecode, StrictEncode, StrictReader, StrictWriter, TypedRead, WriteRaw,
};
use ultrasonic::{AuthToken, CallError, CellAddr, ContractId, Identity, Issue, Operation, Opid, VerifiedOperation};

use crate::deed::{CallParams, DeedBuilder};
use crate::{Articles, EffectiveState, IssueError, ProcessedState, Stock, StockSession, Transition};

pub const DEEDS_VERSION: u16 = 0;

#[derive(Clone, Debug)]
pub struct Ledger<S: Stock>(S, ContractId);

impl<S: Stock> Ledger<S> {
    pub fn new(articles: Articles, conf: S::Conf) -> Result<Self, MultiError<IssueError, S::Error>> {
        let contract_id = articles.contract_id();
        let state = EffectiveState::with_articles(&articles)
            .map_err(|e| IssueError::Genesis(articles.issue().meta.name.clone(), e))
            .map_err(MultiError::A)?;
        let mut stock = S::new(articles, state, conf).map_err(MultiError::B)?;
        let genesis_opid = stock.articles().genesis_opid();
        let mut s = stock.session();
        s.mark_valid(genesis_opid);
        s.commit_transaction().map_err(MultiError::B)?;
        drop(s);
        Ok(Self(stock, contract_id))
    }

    pub fn load(conf: S::Conf) -> Result<Self, S::Error> {
        S::load(conf).map(|stock| {
            let contract_id = stock.articles().contract_id();
            Self(stock, contract_id)
        })
    }

    pub fn config(&self) -> S::Conf { self.0.config() }
    pub fn stock(&self) -> &S { &self.0 }

    #[inline]
    pub fn contract_id(&self) -> ContractId { self.1 }
    #[inline]
    pub fn articles(&self) -> &Articles { self.0.articles() }
    #[inline]
    pub fn state(&self) -> &EffectiveState { self.0.state() }

    /// Opens a session and runs `f` with it, returning the result.
    pub fn with_session<T, E>(&mut self, f: impl FnOnce(&mut S::Session<'_>) -> Result<T, E>) -> Result<T, E> {
        let mut s = self.0.session();
        f(&mut s)
    }

    pub fn is_valid(&mut self, opid: Opid) -> bool { self.0.session().is_valid(opid) }

    pub fn has_operation(&mut self, opid: Opid) -> bool { self.0.session().has_operation(opid) }

    pub fn operation(&mut self, opid: Opid) -> Operation { self.0.session().operation(opid) }

    pub fn operations(&mut self) -> impl Iterator<Item = (Opid, Operation)> {
        self.0
            .session()
            .operations()
            .collect::<Vec<_>>()
            .into_iter()
    }

    pub fn trace_iter(&mut self) -> impl Iterator<Item = (Opid, Transition)> {
        self.0.session().trace().collect::<Vec<_>>().into_iter()
    }

    pub fn read_by(&mut self, addr: CellAddr) -> impl Iterator<Item = Opid> {
        self.0
            .session()
            .read_by(addr)
            .collect::<Vec<_>>()
            .into_iter()
    }

    pub fn spent_by(&mut self, addr: CellAddr) -> Option<Opid> { self.0.session().spent_by(addr) }

    pub fn operation_count(&mut self) -> u64 { self.0.session().operation_count() }

    pub fn transition(&mut self, opid: Opid) -> Transition { self.0.session().transition(opid) }

    /// Ancestors include the original operations.
    pub fn ancestors(&mut self, opids: impl IntoIterator<Item = Opid>) -> impl DoubleEndedIterator<Item = Opid> {
        let mut chain = opids.into_iter().collect::<IndexSet<_>>();
        let genesis_opid = self.0.articles().genesis_opid();
        let mut index = 0usize;
        self.with_session(|session| {
            while let Some(opid) = chain.get_index(index).copied() {
                if opid != genesis_opid {
                    let op = session.operation(opid);
                    for inp in op.immutable_in {
                        if !chain.contains(&inp.opid) {
                            chain.insert(inp.opid);
                        }
                    }
                    for inp in op.destructible_in {
                        if !chain.contains(&inp.addr.opid) {
                            chain.insert(inp.addr.opid);
                        }
                    }
                }
                index += 1;
            }
            Ok::<_, core::convert::Infallible>(())
        })
        .expect("infallible ancestors walk");
        chain.into_iter()
    }

    /// Descendants include the original operations.
    pub fn descendants(&mut self, opids: impl IntoIterator<Item = Opid>) -> impl DoubleEndedIterator<Item = Opid> {
        let mut chain = opids.into_iter().collect::<IndexSet<_>>();
        let mut index = 0usize;
        self.with_session(|session| {
            while let Some(opid) = chain.get_index(index).copied() {
                let op = session.operation(opid);
                for no in 0..op.immutable_out.len_u16() {
                    let addr = CellAddr::new(opid, no);
                    for read in session.read_by(addr).collect::<Vec<_>>() {
                        if !chain.contains(&read) {
                            chain.insert(read);
                        }
                    }
                }
                for no in 0..op.destructible_out.len_u16() {
                    let addr = CellAddr::new(opid, no);
                    if let Some(spent) = session.spent_by(addr) {
                        if !chain.contains(&spent) {
                            chain.insert(spent);
                        }
                    }
                }
                index += 1;
            }
            Ok::<_, core::convert::Infallible>(())
        })
        .expect("infallible descendants walk");
        chain.into_iter()
    }

    pub fn export_all(&mut self, writer: StrictWriter<impl WriteRaw>) -> io::Result<()> {
        let count = self.0.session().operation_count() as u32;
        self.export_internal(count, writer, |_| true, |_, _, w| Ok(w))
    }

    pub fn export_all_aux<W: WriteRaw>(
        &mut self,
        writer: StrictWriter<W>,
        aux: impl FnMut(Opid, &Operation, StrictWriter<W>) -> io::Result<StrictWriter<W>>,
    ) -> io::Result<()> {
        let count = self.0.session().operation_count() as u32;
        self.export_internal(count, writer, |_| true, aux)
    }

    pub fn export(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()> {
        self.export_aux(terminals, writer, |_, _, w| Ok(w))
    }

    pub fn export_aux<W: WriteRaw>(
        &mut self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        writer: StrictWriter<W>,
        aux: impl FnMut(Opid, &Operation, StrictWriter<W>) -> io::Result<StrictWriter<W>>,
    ) -> io::Result<()> {
        let mut queue = terminals
            .into_iter()
            .map(|t| self.0.state().addr(*t.borrow()).opid)
            .collect::<BTreeSet<_>>();
        let articles = self.0.articles();
        let genesis_opid = articles.genesis_opid();
        queue.remove(&genesis_opid);
        let mut opids = queue.clone();

        while let Some(opid) = queue.pop_first() {
            let st = self.0.session().transition(opid);
            for prev in st.destroyed.into_keys().map(|a| a.opid) {
                if !opids.contains(&prev) && prev != genesis_opid {
                    opids.insert(prev);
                    queue.insert(prev);
                }
            }
        }

        let state = self.0.state();
        let articles = self.0.articles();
        let mut collect = |api: &Api, state: &ProcessedState| {
            for (state_name, owned) in &api.global {
                if owned.published {
                    let Some(cells) = state.global.get(state_name) else {
                        continue;
                    };
                    opids.extend(cells.keys().map(|addr| addr.opid));
                }
            }
        };
        collect(&articles.semantics().default, &state.main);
        for (api_name, api) in &articles.semantics().custom {
            let Some(state) = state.aux.get(api_name) else { continue };
            collect(api, state);
        }
        opids.remove(&genesis_opid);

        self.export_internal(opids.len() as u32, writer, |opid| opids.remove(opid), aux)?;

        debug_assert!(opids.is_empty());
        Ok(())
    }

    pub fn export_internal<W: WriteRaw>(
        &mut self,
        count: u32,
        mut writer: StrictWriter<W>,
        mut should_include: impl FnMut(&Opid) -> bool,
        mut aux: impl FnMut(Opid, &Operation, StrictWriter<W>) -> io::Result<StrictWriter<W>>,
    ) -> io::Result<()> {
        let articles = self.0.articles();
        let genesis_opid = articles.genesis_opid();
        let contract_id = self.1;

        writer = (DEEDS_VERSION as u8).strict_encode(writer)?;
        writer = contract_id.strict_encode(writer)?;
        writer = 0u8.strict_encode(writer)?;
        writer = articles.strict_encode(writer)?;
        writer = aux(genesis_opid, &articles.genesis().to_operation(contract_id), writer)?;
        writer = count.strict_encode(writer)?;

        let ops: Vec<(Opid, Operation)> = self.0.session().operations().collect();
        for (opid, op) in ops {
            if !should_include(&opid) {
                continue;
            }
            writer = op.strict_encode(writer)?;
            writer = aux(opid, &op, writer)?;
        }
        Ok(())
    }

    pub fn upgrade_apis(&mut self, new_articles: Articles) -> Result<bool, MultiError<SemanticError, S::Error>> {
        self.0
            .session()
            .update_articles(|articles| articles.upgrade_apis(new_articles))
    }

    pub fn accept<E>(
        &mut self,
        reader: &mut StrictReader<impl ReadRaw>,
        sig_validator: impl FnOnce(StrictHash, &Identity, &SigBlob) -> Result<(), E>,
    ) -> Result<(), MultiError<AcceptError, S::Error>> {
        let count = (|| -> Result<u32, AcceptError> {
            let _ = ReservedBytes::<1, { DEEDS_VERSION as u8 }>::strict_decode(reader)?;
            let contract_id = ContractId::strict_decode(reader)?;
            let ext_blocks = u8::strict_decode(reader)?;
            for _ in 0..ext_blocks {
                let len = u16::strict_decode(reader)?;
                let r = unsafe { reader.raw_reader() };
                let _ = r.read_raw::<{ u16::MAX as usize }>(len as usize)?;
            }
            let semantics = Semantics::strict_decode(reader)?;
            let sig = Option::<SigBlob>::strict_decode(reader)?;
            let issue = Issue::strict_decode(reader)?;
            let articles = Articles::with(semantics, issue, sig, sig_validator)?;
            if articles.contract_id() != contract_id {
                return Err(AcceptError::Articles(SemanticError::ContractMismatch));
            }
            self.upgrade_apis(articles)
                .map_err(|e| AcceptError::Persistence(e.to_string()))?;
            Ok(u32::strict_decode(reader)?)
        })()
        .map_err(MultiError::A)?;

        for _ in 0..=count {
            let op = match Operation::strict_decode(reader) {
                Ok(o) => o,
                Err(DecodeError::Io(e)) if e.kind() == io::ErrorKind::UnexpectedEof => break,
                Err(e) => return Err(MultiError::A(e.into())),
            };
            self.apply_verify(op, false)?;
        }
        self.commit_transaction().map_err(MultiError::B)?;
        Ok(())
    }

    pub fn rollback(&mut self, opids: impl IntoIterator<Item = Opid>) -> Result<(), S::Error> {
        let desc: Vec<Opid> = self.descendants(opids).rev().collect();
        let mut session = self.0.session();
        for opid in desc {
            let mut transition = session.transition(opid);
            let inputs: Vec<CellAddr> = transition.destroyed.keys().copied().collect();
            for addr in inputs {
                if !session.is_valid(addr.opid) {
                    let _ = transition.destroyed.remove(&addr);
                }
            }
            session.update_state(|state, articles| {
                state.rollback(transition, articles.semantics());
            })?;
            session.mark_invalid(opid);
        }
        session.commit_transaction()?;
        Ok(())
    }

    pub fn forward(&mut self, opids: impl IntoIterator<Item = Opid>) -> Result<(), MultiError<AcceptError, S::Error>> {
        let desc: Vec<Opid> = self.descendants(opids).collect();
        let genesis_opid = self.0.articles().genesis_opid();
        for opid in desc {
            let mut session = self.0.session();
            debug_assert!(!session.is_valid(opid));
            let mut chain = IndexSet::from([opid]);
            let mut index = 0usize;
            while let Some(current) = chain.get_index(index).copied() {
                if current != genesis_opid {
                    let op = session.operation(current);
                    for inp in op.immutable_in {
                        if !chain.contains(&inp.opid) {
                            chain.insert(inp.opid);
                        }
                    }
                    for inp in op.destructible_in {
                        if !chain.contains(&inp.addr.opid) {
                            chain.insert(inp.addr.opid);
                        }
                    }
                }
                index += 1;
            }

            let eligible = chain
                .into_iter()
                .filter(|id| *id != opid)
                .all(|id| session.is_valid(id));
            let op = eligible.then(|| session.operation(opid));
            drop(session);

            if let Some(op) = op {
                self.apply_verify(op, true)?;
            }
        }
        self.commit_transaction().map_err(MultiError::B)?;
        Ok(())
    }

    pub fn start_deed(&mut self, method: impl Into<MethodName>) -> DeedBuilder<'_, S> {
        let builder = OpBuilder::new(self.contract_id(), self.0.articles().call_id(method));
        DeedBuilder { builder, ledger: self }
    }

    pub fn call(&mut self, params: CallParams) -> Result<Opid, MultiError<AcceptError, S::Error>> {
        let mut builder = self.start_deed(params.core.method);
        for NamedState { name, state } in params.core.global {
            builder = builder.append(name, state.verified, state.unverified);
        }
        for NamedState { name, state } in params.core.owned {
            builder = builder.assign(name, state.auth, state.data, state.lock);
        }
        for addr in params.reading {
            builder = builder.reading(addr);
        }
        for (addr, satisfaction) in params.using {
            if let Some(s) = satisfaction {
                builder = builder.satisfying(addr, s.name, s.witness);
            } else {
                builder = builder.using(addr);
            }
        }
        builder.commit()
    }

    pub fn apply_verify(
        &mut self,
        operation: Operation,
        force: bool,
    ) -> Result<bool, MultiError<AcceptError, S::Error>> {
        if operation.contract_id != self.contract_id() {
            return Err(MultiError::A(AcceptError::Articles(SemanticError::ContractMismatch)));
        }
        let opid = operation.opid();
        let present = self.0.session().is_valid(opid);
        if !present || force {
            let verified = self
                .0
                .articles()
                .codex()
                .verify(self.contract_id(), operation, &self.0.state().raw, self.0.articles())
                .map_err(AcceptError::from)
                .map_err(MultiError::A)?;
            self.apply_internal(opid, verified, present && !force)
                .map_err(MultiError::B)?;
        }
        Ok(present)
    }

    pub fn apply(&mut self, operation: VerifiedOperation) -> Result<Transition, S::Error> {
        let opid = operation.opid();
        let present = self.0.session().is_valid(opid);
        self.apply_internal(opid, operation, present)
    }

    fn apply_internal(
        &mut self,
        opid: Opid,
        operation: VerifiedOperation,
        present: bool,
    ) -> Result<Transition, S::Error> {
        let mut s = self.0.session();
        if !present {
            s.add_operation(opid, operation.as_operation());
        }
        let op = operation.as_operation();
        for read in &op.immutable_in {
            s.add_reading(*read, opid);
        }
        for prevout in &op.destructible_in {
            s.add_spending(prevout.addr, opid);
        }
        let transition = s.update_state(|state, articles| state.apply(operation, articles.semantics()))?;
        s.add_transition(opid, &transition);
        s.mark_valid(opid);
        Ok(transition)
    }

    pub fn commit_transaction(&mut self) -> Result<(), S::Error> { self.0.session().commit_transaction() }
}

#[derive(Debug, Display, Error, From)]
#[display(inner)]
pub enum AcceptError {
    #[from]
    Io(io::Error),
    #[from]
    Articles(SemanticError),
    #[from]
    Verify(CallError),
    #[from]
    Decode(DecodeError),
    #[from]
    Serialize(SerializeError),
    Persistence(String),
    #[cfg(feature = "binfile")]
    #[display("Invalid file format")]
    InvalidFileFormat,
}

#[cfg(feature = "binfile")]
mod _fs {
    use std::path::Path;

    use binfile::BinFile;
    use strict_encoding::{StreamReader, StreamWriter};

    use super::*;

    pub const DEEDS_MAGIC_NUMBER: u64 = u64::from_be_bytes(*b"DEEDLDGR");

    impl<S: Stock> Ledger<S> {
        pub fn export_all_to_file(&mut self, output: impl AsRef<Path>) -> io::Result<()> {
            let file = BinFile::<DEEDS_MAGIC_NUMBER, DEEDS_VERSION>::create_new(output)?;
            self.export_all(StrictWriter::with(StreamWriter::new::<{ usize::MAX }>(file)))
        }

        pub fn export_to_file(
            &mut self,
            terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
            output: impl AsRef<Path>,
        ) -> io::Result<()> {
            let file = BinFile::<DEEDS_MAGIC_NUMBER, DEEDS_VERSION>::create_new(output)?;
            self.export(terminals, StrictWriter::with(StreamWriter::new::<{ usize::MAX }>(file)))
        }

        pub fn accept_from_file<E>(
            &mut self,
            input: impl AsRef<Path>,
            sig_validator: impl FnOnce(StrictHash, &Identity, &SigBlob) -> Result<(), E>,
        ) -> Result<(), MultiError<AcceptError, S::Error>> {
            let file = BinFile::<DEEDS_MAGIC_NUMBER, DEEDS_VERSION>::open(input)
                .map_err(|_| AcceptError::InvalidFileFormat)
                .map_err(MultiError::from_a)?;
            let mut reader = StrictReader::with(StreamReader::new::<{ usize::MAX }>(file));
            self.accept(&mut reader, sig_validator)
        }
    }
}
#[cfg(feature = "binfile")]
pub use _fs::*;
