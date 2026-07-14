// SONIC: Standard library for formally-verifiable distributed contracts
//
// SPDX-License-Identifier: Apache-2.0

use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use core::borrow::Borrow;
use std::collections::{HashMap, VecDeque};
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

    pub fn operation(&mut self, opid: Opid) -> Operation {
        Arc::unwrap_or_clone(self.0.session().operation(opid))
    }

    /// Shared-ownership variant of [`Self::operation`]: returns the reference-counted operation
    /// without cloning the operation data. Use it when the operation is only read (e.g. to
    /// inspect its output count) so the shared allocation is not deep-copied.
    pub fn operation_arc(&mut self, opid: Opid) -> Arc<Operation> { self.0.session().operation(opid) }

    pub fn operations(&mut self) -> impl Iterator<Item = (Opid, Operation)> {
        self.0.session().operations().into_iter()
    }

    pub fn valid_opids(&mut self) -> Vec<Opid> { self.0.session().valid_opids() }

    pub fn operation_parent_ops(&mut self) -> Vec<(Opid, Vec<Opid>)> { self.0.session().operation_parent_ops() }

    pub fn operation_output_counts(&mut self) -> Vec<(Opid, u16)> { self.0.session().operation_output_counts() }

    pub fn trace_iter(&mut self) -> impl Iterator<Item = (Opid, Transition)> { self.0.session().trace().into_iter() }

    pub fn read_by(&mut self, addr: CellAddr) -> impl Iterator<Item = Opid> {
        self.0.session().read_by(addr).into_iter()
    }

    pub fn spent_by(&mut self, addr: CellAddr) -> Option<Opid> { self.0.session().spent_by(addr) }

    pub fn operation_count(&mut self) -> u64 { self.0.session().operation_count() }

    pub fn transition(&mut self, opid: Opid) -> Transition {
        Arc::unwrap_or_clone(self.0.session().transition(opid))
    }

    /// Ancestors include the original operations.
    pub fn ancestors(&mut self, opids: impl IntoIterator<Item = Opid>) -> impl DoubleEndedIterator<Item = Opid> {
        let mut chain = opids.into_iter().collect::<IndexSet<_>>();
        let genesis_opid = self.0.articles().genesis_opid();
        let mut index = 0usize;
        self.with_session(|session| {
            while let Some(opid) = chain.get_index(index).copied() {
                if opid != genesis_opid {
                    let op = session.operation(opid);
                    for inp in &op.immutable_in {
                        if !chain.contains(&inp.opid) {
                            chain.insert(inp.opid);
                        }
                    }
                    for inp in &op.destructible_in {
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
                    for read in session.read_by(addr) {
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
        self.export_all_aux(writer, |_, _, writer| Ok(writer))
    }

    pub fn export_all_aux<W: WriteRaw>(
        &mut self,
        writer: StrictWriter<W>,
        aux: impl FnMut(Opid, &Operation, StrictWriter<W>) -> io::Result<StrictWriter<W>>,
    ) -> io::Result<()> {
        let genesis_opid = self.0.articles().genesis_opid();
        let operations = self.0.session().operations();
        let seeds = operations.iter().map(|(opid, _)| *opid).collect::<Vec<_>>();
        let plan = ExportPlan::build(operations, genesis_opid, seeds)?;
        self.export_ordered(plan, writer, aux)
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
        let articles = self.0.articles();
        let genesis_opid = articles.genesis_opid();

        // Published-state producers are roots of the exported view just like terminal owners.
        // Merge all roots before walking ancestors so published operations bring their complete
        // dependency closure with them.
        let mut seeds = terminals
            .into_iter()
            .map(|terminal| self.0.state().addr(*terminal.borrow()).opid)
            .collect::<BTreeSet<_>>();
        let state = self.0.state();
        let mut collect = |api: &Api, state: &ProcessedState| {
            for (state_name, owned) in &api.global {
                if owned.published {
                    let Some(cells) = state.global.get(state_name) else {
                        continue;
                    };
                    seeds.extend(cells.keys().map(|addr| addr.opid));
                }
            }
        };
        collect(&articles.semantics().default, &state.main);
        for (api_name, api) in &articles.semantics().custom {
            let Some(state) = state.aux.get(api_name) else { continue };
            collect(api, state);
        }
        seeds.remove(&genesis_opid);

        // One session read is important for database stocks: it provides a consistent snapshot
        // and avoids an operation lookup per dependency edge.
        let operations = self.0.session().operations();
        let plan = ExportPlan::build(operations, genesis_opid, seeds)?;
        self.export_ordered(plan, writer, aux)
    }

    fn export_ordered<W: WriteRaw>(
        &self,
        plan: ExportPlan,
        mut writer: StrictWriter<W>,
        mut aux: impl FnMut(Opid, &Operation, StrictWriter<W>) -> io::Result<StrictWriter<W>>,
    ) -> io::Result<()> {
        let articles = self.0.articles();
        let genesis_opid = articles.genesis_opid();
        let contract_id = self.1;
        let count = u32::try_from(plan.operations.len())
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "too many operations to export"))?;

        writer = (DEEDS_VERSION as u8).strict_encode(writer)?;
        writer = contract_id.strict_encode(writer)?;
        writer = 0u8.strict_encode(writer)?;
        writer = articles.strict_encode(writer)?;
        writer = aux(genesis_opid, &articles.genesis().to_operation(contract_id), writer)?;
        writer = count.strict_encode(writer)?;

        for (opid, op) in plan.operations {
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
            let transition_mut = Arc::make_mut(&mut transition);
            let inputs: Vec<CellAddr> = transition_mut.destroyed.keys().copied().collect();
            for addr in inputs {
                if !session.is_valid(addr.opid) {
                    let _ = transition_mut.destroyed.remove(&addr);
                }
            }
            session.update_state(|state, articles| {
                state.rollback(Arc::unwrap_or_clone(transition), articles.semantics());
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
                    for inp in &op.immutable_in {
                        if !chain.contains(&inp.opid) {
                            chain.insert(inp.opid);
                        }
                    }
                    for inp in &op.destructible_in {
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
        operation: impl Into<Arc<Operation>>,
        force: bool,
    ) -> Result<bool, MultiError<AcceptError, S::Error>> {
        let operation = operation.into();
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

    pub fn preload_apply_insert_lookups<'a>(&mut self, operations: impl IntoIterator<Item = &'a Operation>) {
        self.0.session().preload_apply_insert_lookups(operations);
    }

    fn apply_internal(
        &mut self,
        opid: Opid,
        operation: VerifiedOperation,
        present: bool,
    ) -> Result<Transition, S::Error> {
        let mut s = self.0.session();
        if !present {
            s.add_operation(opid, operation.operation_arc());
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

/// A fully validated export snapshot.
///
/// Building the plan before writing the stream keeps persistence enumeration out of the wire
/// format contract: the stash may be returned in any order, while consumers still receive every
/// producer before the operations which read or destroy its cells.
#[derive(Debug)]
struct ExportPlan {
    operations: Vec<(Opid, Operation)>,
}

impl ExportPlan {
    fn build(
        operations: Vec<(Opid, Operation)>,
        genesis_opid: Opid,
        seeds: impl IntoIterator<Item = Opid>,
    ) -> io::Result<Self> {
        let invalid = |message: String| io::Error::new(io::ErrorKind::InvalidData, message);
        let mut index_by_opid = HashMap::with_capacity(operations.len());

        for (index, (stored_opid, operation)) in operations.iter().enumerate() {
            let committed_opid = operation.opid();
            if *stored_opid != committed_opid {
                return Err(invalid(format!(
                    "operation stash key {stored_opid} does not match committed operation id {committed_opid}"
                )));
            }
            if index_by_opid.insert(*stored_opid, index).is_some() {
                return Err(invalid(format!(
                    "duplicate operation {stored_opid} in the contract stash"
                )));
            }
        }

        let parents = |operation: &Operation| {
            operation
                .destructible_in
                .iter()
                .map(|input| input.addr.opid)
                .chain(operation.immutable_in.iter().map(|addr| addr.opid))
                .collect::<BTreeSet<_>>()
        };

        // Compute the complete ancestor closure from committed operation inputs. Transition
        // traces are derived persistence data and may be incomplete after import or recovery.
        let mut included = vec![false; operations.len()];
        let mut pending = VecDeque::new();
        for seed in seeds {
            if seed == genesis_opid {
                continue;
            }
            let &index = index_by_opid.get(&seed).ok_or_else(|| {
                invalid(format!("operation {seed} is missing from the contract stash"))
            })?;
            if !included[index] {
                included[index] = true;
                pending.push_back(index);
            }
        }

        while let Some(index) = pending.pop_front() {
            let (opid, operation) = &operations[index];
            for parent in parents(operation) {
                if parent == genesis_opid {
                    continue;
                }
                let &parent_index = index_by_opid.get(&parent).ok_or_else(|| {
                    invalid(format!(
                        "operation {opid} references parent operation {parent} which is missing from the contract stash"
                    ))
                })?;
                if !included[parent_index] {
                    included[parent_index] = true;
                    pending.push_back(parent_index);
                }
            }
        }

        // Stable Kahn sort. The original stash position is only a tie-breaker between unrelated
        // operations, so an already dependency-ordered stash is emitted unchanged.
        let mut children = vec![Vec::new(); operations.len()];
        let mut indegrees = vec![0usize; operations.len()];
        for (index, (_, operation)) in operations.iter().enumerate() {
            if !included[index] {
                continue;
            }
            for parent in parents(operation) {
                if parent == genesis_opid {
                    continue;
                }
                let parent_index = index_by_opid[&parent];
                children[parent_index].push(index);
                indegrees[index] += 1;
            }
        }

        let mut ready = indegrees
            .iter()
            .enumerate()
            .filter(|&(index, &indegree)| included[index] && indegree == 0)
            .map(|(index, _)| index)
            .collect::<BTreeSet<_>>();
        let included_count = included.iter().filter(|&&value| value).count();
        let mut order = Vec::with_capacity(included_count);
        while let Some(index) = ready.pop_first() {
            order.push(index);
            for &child in &children[index] {
                indegrees[child] -= 1;
                if indegrees[child] == 0 {
                    ready.insert(child);
                }
            }
        }
        if order.len() != included_count {
            return Err(invalid(
                "contract stash contains a dependency cycle between operations".to_owned(),
            ));
        }

        let mut slots = operations.into_iter().map(Some).collect::<Vec<_>>();
        let operations = order
            .into_iter()
            .map(|index| {
                slots[index]
                    .take()
                    .expect("topological order visits each operation once")
            })
            .collect();
        Ok(Self { operations })
    }
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

#[cfg(test)]
mod tests {
    #![cfg_attr(coverage_nightly, coverage(off))]

    use amplify::confinement::SmallVec;
    use ultrasonic::{Input, StateValue, fe256};

    use super::*;

    fn contract_id() -> ContractId { ContractId::from([0xC0; 32]) }

    fn make_op(nonce: u64, destructible: &[CellAddr], immutable: &[CellAddr]) -> (Opid, Operation) {
        let mut destructible_in = SmallVec::new();
        for addr in destructible {
            destructible_in
                .push(Input {
                    addr: *addr,
                    witness: StateValue::None,
                })
                .unwrap();
        }
        let mut immutable_in = SmallVec::new();
        for addr in immutable {
            immutable_in.push(*addr).unwrap();
        }
        let operation = Operation {
            version: default!(),
            contract_id: contract_id(),
            call_id: 0,
            nonce: fe256::from(nonce),
            witness: StateValue::None,
            destructible_in,
            immutable_in,
            destructible_out: none!(),
            immutable_out: none!(),
        };
        (operation.opid(), operation)
    }

    fn genesis() -> Opid { make_op(u64::MAX, &[], &[]).0 }

    fn opids(plan: ExportPlan) -> Vec<Opid> {
        plan.operations.into_iter().map(|(opid, _)| opid).collect()
    }

    #[test]
    fn consumer_first_stash_is_dependency_ordered_for_both_input_kinds() {
        let genesis = genesis();
        let (producer_id, producer) = make_op(1, &[CellAddr::new(genesis, 0)], &[]);
        let (middle_id, middle) = make_op(2, &[CellAddr::new(producer_id, 0)], &[]);
        let (consumer_id, consumer) = make_op(
            3,
            &[CellAddr::new(middle_id, 0)],
            &[CellAddr::new(producer_id, 1)],
        );

        let plan = ExportPlan::build(
            vec![(consumer_id, consumer), (middle_id, middle), (producer_id, producer)],
            genesis,
            [consumer_id],
        )
        .unwrap();
        assert_eq!(opids(plan), vec![producer_id, middle_id, consumer_id]);
    }

    #[test]
    fn published_seed_gets_its_complete_ancestor_closure() {
        let genesis = genesis();
        let (producer_id, producer) = make_op(1, &[CellAddr::new(genesis, 0)], &[]);
        let (published_id, published) = make_op(2, &[], &[CellAddr::new(producer_id, 0)]);

        let plan = ExportPlan::build(
            vec![(published_id, published), (producer_id, producer)],
            genesis,
            [published_id],
        )
        .unwrap();
        assert_eq!(opids(plan), vec![producer_id, published_id]);
    }

    #[test]
    fn unrelated_operations_keep_stash_order() {
        let genesis = genesis();
        let (first_id, first) = make_op(1, &[CellAddr::new(genesis, 0)], &[]);
        let (second_id, second) = make_op(2, &[CellAddr::new(genesis, 1)], &[]);
        let (third_id, third) = make_op(3, &[CellAddr::new(genesis, 2)], &[]);

        let plan = ExportPlan::build(
            vec![(third_id, third), (first_id, first), (second_id, second)],
            genesis,
            [third_id, first_id, second_id],
        )
        .unwrap();
        assert_eq!(opids(plan), vec![third_id, first_id, second_id]);
    }

    #[test]
    fn missing_parent_and_mismatched_stash_key_fail_closed() {
        let genesis = genesis();
        let (missing_id, _) = make_op(1, &[CellAddr::new(genesis, 0)], &[]);
        let (consumer_id, consumer) = make_op(2, &[CellAddr::new(missing_id, 0)], &[]);
        let missing = ExportPlan::build(vec![(consumer_id, consumer)], genesis, [consumer_id])
            .unwrap_err();
        assert_eq!(missing.kind(), io::ErrorKind::InvalidData);

        let (actual_id, operation) = make_op(3, &[CellAddr::new(genesis, 1)], &[]);
        let wrong_id = make_op(4, &[CellAddr::new(genesis, 2)], &[]).0;
        assert_ne!(actual_id, wrong_id);
        let mismatched = ExportPlan::build(vec![(wrong_id, operation)], genesis, [wrong_id])
            .unwrap_err();
        assert_eq!(mismatched.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn duplicate_keys_and_corrupt_cycles_fail_closed() {
        let genesis = genesis();
        let (opid, operation) = make_op(1, &[CellAddr::new(genesis, 0)], &[]);
        let duplicate = ExportPlan::build(
            vec![(opid, operation.clone()), (opid, operation)],
            genesis,
            [opid],
        )
        .unwrap_err();
        assert_eq!(duplicate.kind(), io::ErrorKind::InvalidData);

        let first_key = Opid::from([0x01; 32]);
        let second_key = Opid::from([0x02; 32]);
        let (_, first) = make_op(2, &[CellAddr::new(second_key, 0)], &[]);
        let (_, second) = make_op(3, &[CellAddr::new(first_key, 0)], &[]);
        let cycle = ExportPlan::build(
            vec![(first_key, first), (second_key, second)],
            genesis,
            [first_key],
        )
        .unwrap_err();
        assert_eq!(cycle.kind(), io::ErrorKind::InvalidData);
    }
}
