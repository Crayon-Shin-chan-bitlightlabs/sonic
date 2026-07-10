// SONIC: Standard library for formally-verifiable distributed contracts
//
// SPDX-License-Identifier: Apache-2.0
//
// Designed in 2019-2025 by Dr Maxim Orlovsky <orlovsky@ubideco.org>
// Written in 2024-2025 by Dr Maxim Orlovsky <orlovsky@ubideco.org>
//
// Copyright (C) 2019-2024 LNP/BP Standards Association, Switzerland.
// Copyright (C) 2024-2025 Laboratories for Ubiquitous Deterministic Computing (UBIDECO),
//                         Institute for Distributed and Cognitive Systems (InDCS), Switzerland.
// Copyright (C) 2019-2025 Dr Maxim Orlovsky.
// All rights under the above copyrights are reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
// in compliance with the License. You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
// or implied. See the License for the specific language governing permissions and limitations under
// the License.

use alloc::collections::BTreeSet;
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
use crate::{Articles, EffectiveState, IssueError, ProcessedState, Stock, Transition};

pub const DEEDS_VERSION: u16 = 0;

/// Contract with all its state and operations, supporting updates and rollbacks.
// We need this structure to hide internal persistence methods and not to expose them.
// We need the persistence trait (`Stock`) in order to allow different persistence storage
// implementations.
#[derive(Clone, Debug)]
pub struct Ledger<S: Stock>(S, /** Cached value */ ContractId);

impl<S: Stock> Ledger<S> {
    /// Instantiates a new contract from the provided articles, creating its persistence with the
    /// provided configuration.
    ///
    /// # Panics
    ///
    /// This call must not panic, and instead must return an error.
    ///
    /// # Blocking I/O
    ///
    /// This call MAY perform any I/O operations.
    pub fn new(articles: Articles, conf: S::Conf) -> Result<Self, MultiError<IssueError, S::Error>> {
        let contract_id = articles.contract_id();
        let state = EffectiveState::with_articles(&articles)
            .map_err(|e| IssueError::Genesis(articles.issue().meta.name.clone(), e))
            .map_err(MultiError::A)?;
        let mut stock = S::new(articles, state, conf).map_err(MultiError::B)?;
        let genesis_opid = stock.articles().genesis_opid();
        stock.mark_valid(genesis_opid);
        stock.commit_transaction();
        Ok(Self(stock, contract_id))
    }

    /// Loads a contract using the provided configuration for persistence.
    ///
    /// # Panics
    ///
    /// This call must not panic, and instead must return an error.
    ///
    /// # Blocking I/O
    ///
    /// This call MAY perform any I/O operations.
    pub fn load(conf: S::Conf) -> Result<Self, S::Error> {
        S::load(conf).map(|stock| {
            let contract_id = stock.articles().contract_id();
            Self(stock, contract_id)
        })
    }

    pub fn config(&self) -> S::Conf { self.0.config() }

    pub fn stock(&self) -> &S { &self.0 }

    /// Provides contract id.
    ///
    /// The contract id value is cached; thus, calling this operation is inexpensive.
    ///
    /// # Blocking I/O
    ///
    /// This call MUST NOT perform any I/O operations and MUST BE a non-blocking.
    #[inline]
    pub fn contract_id(&self) -> ContractId { self.1 }

    /// Provides contract [`Articles`], which include contract genesis.
    ///
    /// # Blocking I/O
    ///
    /// This call MUST NOT perform any I/O operations and MUST BE a non-blocking.
    #[inline]
    pub fn articles(&self) -> &Articles { self.0.articles() }

    /// Provides contract [`EffectiveState`].
    ///
    /// # Blocking I/O
    ///
    /// This call MUST NOT perform any I/O operations and MUST BE a non-blocking.
    #[inline]
    pub fn state(&self) -> &EffectiveState { self.0.state() }

    /// Detects whether an operation with a given `opid` participates in the current state.
    pub fn is_valid(&self, opid: Opid) -> bool { self.0.is_valid(opid) }

    /// Detects whether an operation with a given `opid` is known to the contract.
    ///
    /// # Nota bene
    ///
    /// Does not include genesis operation id.
    ///
    /// Positive response doesn't indicate that the operation participates in the current contract
    /// state or in a current valid contract history, which may be exported.
    ///
    /// Operations may be excluded from the history due to rollbacks (see [`Ledger::rollback`]),
    /// as well as re-included later with forwards (see [`Ledger::forward`]). In both cases
    /// they are kept in the contract storage ("stash") and remain accessible to this method.
    ///
    /// # Blocking I/O
    ///
    /// This call MAY BE blocking.
    #[inline]
    pub fn has_operation(&self, opid: Opid) -> bool { self.0.has_operation(opid) }

    /// Returns an operation ([`Operation`]) with a given `opid` from the set of known contract
    /// operations ("stash").
    ///
    /// # Nota bene
    ///
    /// Does not include genesis operation.
    ///
    /// If the method returns an operation, this doesn't indicate that the operation participates in
    /// the current contract state or in a current valid contract history, which/ may be exported.
    ///
    /// Operations may be excluded from the history due to rollbacks (see [`Ledger::rollback`]),
    /// as well as re-included later with forwards (see [`Ledger::forward`]). In both cases
    /// they are kept in the contract storage ("stash") and remain accessible to this method.
    ///
    /// # Panics
    ///
    /// If an `opid` is not present in the contract stash, or it corresponds to the genesis
    /// operation.
    ///
    /// In order to avoid panics always call the method after calling `has_operation`.
    ///
    /// # Blocking I/O
    ///
    /// This call MAY BE blocking.
    #[inline]
    pub fn operation(&self, opid: Opid) -> Operation { self.0.operation(opid) }

    /// Returns an iterator over all operations known to the contract (i.e., the complete contract
    /// stash).
    ///
    /// # Nota bene
    ///
    /// Does not include genesis operation.
    ///
    /// Contract stash is a broader concept than contract history. It includes operations which may
    /// not contribute to the current contract state or participate in the contract history, which
    /// may be exported.
    ///
    /// Operations may be excluded from the history due to rollbacks (see [`Ledger::rollback`]),
    /// as well as re-included later with forwards (see [`Ledger::forward`]). In both cases
    /// they are kept in the contract storage ("stash") and remain accessible to this method.
    ///
    /// # Panics
    ///
    /// The method MUST NOT panic
    ///
    /// # Blocking I/O
    ///
    /// The iterator provided in return may be a blocking iterator.
    #[inline]
    pub fn operations(&self) -> impl Iterator<Item = (Opid, Operation)> + use<'_, S> { self.0.operations() }

    /// Returns an iterator over all state transitions known to the contract (i.e., the complete
    /// contract trace).
    ///
    /// # Nota bene
    ///
    /// Contract trace is a broader concept than contract history. It includes state transition
    /// which may not contribute to the current contract state or participate in the contract
    /// history, which may be exported.
    ///
    /// State transitions may be excluded from the history due to rollbacks (see
    /// [`Ledger::rollback`]), as well as re-included later with forwards (see
    /// [`Ledger::forward`]). In both cases corresponding state transitions are kept in the
    /// contract storage ("stash") and remain accessible to this method.
    ///
    /// # Panics
    ///
    /// The method MUST NOT panic
    ///
    /// # Blocking I/O
    ///
    /// The iterator provided in return may be a blocking iterator.
    #[inline]
    pub fn trace(&self) -> impl Iterator<Item = (Opid, Transition)> + use<'_, S> { self.0.trace() }

    #[inline]
    pub fn read_by(&self, addr: CellAddr) -> impl Iterator<Item = Opid> + use<'_, S> { self.0.read_by(addr) }
    #[inline]
    pub fn spent_by(&self, addr: CellAddr) -> Option<Opid> { self.0.spent_by(addr) }

    /// # Nota bene
    ///
    /// Ancestors do include the original operations
    pub fn ancestors(&self, opids: impl IntoIterator<Item = Opid>) -> impl DoubleEndedIterator<Item = Opid> {
        let mut chain = opids.into_iter().collect::<IndexSet<_>>();
        // Get all subsequent operations
        let mut index = 0usize;
        let genesis_opid = self.articles().genesis_opid();
        while let Some(opid) = chain.get_index(index).copied() {
            if opid != genesis_opid {
                let op = self.0.operation(opid);
                for inp in op.immutable_in {
                    let parent = inp.opid;
                    if !chain.contains(&parent) {
                        chain.insert(parent);
                    }
                }
                for inp in op.destructible_in {
                    let parent = inp.addr.opid;
                    if !chain.contains(&parent) {
                        chain.insert(parent);
                    }
                }
            }
            index += 1;
        }
        chain.into_iter()
    }

    /// # Nota bene
    ///
    /// Descendants do include the original operations
    pub fn descendants(&self, opids: impl IntoIterator<Item = Opid>) -> impl DoubleEndedIterator<Item = Opid> {
        let mut chain = opids.into_iter().collect::<IndexSet<_>>();
        // Get all subsequent operations
        let mut index = 0usize;
        while let Some(opid) = chain.get_index(index).copied() {
            let op = self.0.operation(opid);
            for no in 0..op.immutable_out.len_u16() {
                let addr = CellAddr::new(opid, no);
                for read in self.0.read_by(addr) {
                    if !chain.contains(&read) {
                        chain.insert(read);
                    }
                }
            }
            for no in 0..op.destructible_out.len_u16() {
                let addr = CellAddr::new(opid, no);
                let Some(spent) = self.0.spent_by(addr) else { continue };
                if !chain.contains(&spent) {
                    chain.insert(spent);
                }
            }
            index += 1;
        }
        chain.into_iter()
    }

    /// Exports contract with all known operations.
    pub fn export_all(&self, writer: StrictWriter<impl WriteRaw>) -> io::Result<()> {
        self.export_all_aux(writer, |_, _, w| Ok(w))
    }

    /// Exports contract with all known operations with some auxiliary information returned by
    /// `aux`.
    pub fn export_all_aux<W: WriteRaw>(
        &self,
        writer: StrictWriter<W>,
        aux: impl FnMut(Opid, &Operation, StrictWriter<W>) -> io::Result<StrictWriter<W>>,
    ) -> io::Result<()> {
        let genesis_opid = self.articles().genesis_opid();
        let operations = self.0.operations().collect::<Vec<_>>();
        let seeds = operations.iter().map(|(opid, _)| *opid).collect::<Vec<_>>();
        let ops = plan_export(operations, genesis_opid, seeds)?;
        self.export_ordered(ops, writer, aux)
    }

    /// Export a part of a contract history: a graph between a set of terminals and genesis.
    pub fn export(
        &self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        writer: StrictWriter<impl WriteRaw>,
    ) -> io::Result<()> {
        self.export_aux(terminals, writer, |_, _, w| Ok(w))
    }

    /// Exports contract and operations to a stream, extending operation data with some auxiliary
    /// information returned by `aux`.
    pub fn export_aux<W: WriteRaw>(
        &self,
        terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
        writer: StrictWriter<W>,
        aux: impl FnMut(Opid, &Operation, StrictWriter<W>) -> io::Result<StrictWriter<W>>,
    ) -> io::Result<()> {
        let articles = self.articles();
        let genesis_opid = articles.genesis_opid();

        // Seeds are terminals plus all operations defining published state. Both must be merged
        // before computing the ancestor closure, so that ancestors of published-state operations
        // are included in the consignment as well.
        let mut seeds = terminals
            .into_iter()
            .map(|terminal| self.0.state().addr(*terminal.borrow()).opid)
            .collect::<BTreeSet<_>>();
        let state = self.state();
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
            let Some(state) = state.aux.get(api_name) else {
                continue;
            };
            collect(api, state);
        }
        seeds.remove(&genesis_opid);

        // Load the stash in one pass: resolving operations one by one may cause a separate
        // storage query per operation on database-backed stocks.
        let operations = self.0.operations().collect::<Vec<_>>();
        let ops = plan_export(operations, genesis_opid, seeds)?;
        self.export_ordered(ops, writer, aux)
    }

    /// Writes a consignment stream containing the given operations in the given order.
    ///
    /// The operation count is derived from `ops`, and all inclusion decisions are made by the
    /// caller before any byte is written, so a failure can't leave a partially-written stream
    /// with a wrong operation count.
    fn export_ordered<W: WriteRaw>(
        &self,
        ops: Vec<(Opid, Operation)>,
        mut writer: StrictWriter<W>,
        mut aux: impl FnMut(Opid, &Operation, StrictWriter<W>) -> io::Result<StrictWriter<W>>,
    ) -> io::Result<()> {
        let count = u32::try_from(ops.len())
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "too many operations to export"))?;
        let articles = self.articles();
        let genesis_opid = articles.genesis_opid();

        // Write version number
        writer = (DEEDS_VERSION as u8).strict_encode(writer)?;
        // Write contract id
        let contract_id = self.contract_id();
        writer = self.contract_id().strict_encode(writer)?;
        // Write an empty extension block
        writer = 0u8.strict_encode(writer)?;
        // Write articles
        writer = articles.strict_encode(writer)?;
        writer = aux(genesis_opid, &articles.genesis().to_operation(contract_id), writer)?;
        // Write no of operations
        writer = count.strict_encode(writer)?;
        // Stream operations
        for (opid, op) in ops {
            writer = op.strict_encode(writer)?;
            writer = aux(opid, &op, writer)?;
        }
        Ok(())
    }

    pub fn upgrade_apis(&mut self, new_articles: Articles) -> Result<bool, MultiError<SemanticError, S::Error>> {
        self.0
            .update_articles(|articles| articles.upgrade_apis(new_articles))
    }

    pub fn accept<E>(
        &mut self,
        reader: &mut StrictReader<impl ReadRaw>,
        sig_validator: impl FnOnce(StrictHash, &Identity, &SigBlob) -> Result<(), E>,
    ) -> Result<(), MultiError<AcceptError, S::Error>> {
        // We need this closure to avoid multiple `map_err`.
        let count = (|| -> Result<u32, AcceptError> {
            // Check version number
            let _ = ReservedBytes::<1, { DEEDS_VERSION as u8 }>::strict_decode(reader)?;

            let contract_id = ContractId::strict_decode(reader)?;

            // Read and ignore the extension block
            let ext_blocks = u8::strict_decode(reader)?;
            for _ in 0..ext_blocks {
                let len = u16::strict_decode(reader)?;
                let r = unsafe { reader.raw_reader() };
                let _ = r.read_raw::<{ u16::MAX as usize }>(len as usize)?;
            }

            // Read articles
            let semantics = Semantics::strict_decode(reader)?;
            let sig = Option::<SigBlob>::strict_decode(reader)?;
            let issue = Issue::strict_decode(reader)?;
            let articles = Articles::with(semantics, issue, sig, sig_validator)?;
            if articles.contract_id() != contract_id {
                return Err(AcceptError::Articles(SemanticError::ContractMismatch));
            }

            self.upgrade_apis(articles)
                .map_err(|e| AcceptError::Persistence(e.to_string()))?;

            let count = u32::strict_decode(reader)?;
            Ok(count)
        })()
        .map_err(MultiError::A)?;

        // We need to account for genesis, which is not included in the `count`
        for _ in 0..=count {
            let op = match Operation::strict_decode(reader) {
                Ok(operation) => operation,
                Err(DecodeError::Io(e)) if e.kind() == io::ErrorKind::UnexpectedEof => break,
                Err(e) => return Err(MultiError::A(e.into())),
            };
            self.apply_verify(op, false)?;
        }
        // Here we do not check for the end of the stream,
        // so in the future we can have arbitrary extensions
        // put here with no backward compatibility issues.
        self.commit_transaction();
        Ok(())
    }

    pub fn rollback(&mut self, opids: impl IntoIterator<Item = Opid>) -> Result<(), S::Error> {
        for opid in self.descendants(opids).rev() {
            let mut transition = self.0.transition(opid);
            // We need to filter out already invalidated inputs
            let inputs = transition
                .destroyed
                .keys()
                .copied()
                .collect::<IndexSet<_>>();
            for addr in inputs {
                if !self.is_valid(addr.opid) {
                    // empty destroyed is allowed
                    let _ = transition.destroyed.remove(&addr);
                }
            }
            self.0.update_state(|state, articles| {
                state.rollback(transition, articles.semantics());
            })?;
            self.0.mark_invalid(opid);
        }
        self.commit_transaction();
        Ok(())
    }

    pub fn forward(&mut self, opids: impl IntoIterator<Item = Opid>) -> Result<(), MultiError<AcceptError, S::Error>> {
        for opid in self.descendants(opids) {
            debug_assert!(!self.is_valid(opid));
            if self
                .ancestors([opid])
                .filter(|id| *id != opid)
                .all(|id| self.is_valid(id))
            {
                let op = self.0.operation(opid);
                self.apply_verify(op, true)?;
                debug_assert!(self.is_valid(opid));
            }
        }
        self.commit_transaction();
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
            if let Some(satisfaction) = satisfaction {
                builder = builder.satisfying(addr, satisfaction.name, satisfaction.witness);
            } else {
                builder = builder.using(addr);
            }
        }

        builder.commit()
    }

    /// Adds operation which was already checked to the stock. This does the following:
    /// - includes raw operation to stash;
    /// - computes state modification and applies it to the state;
    /// - saves removed state as a [`Transition`] and adds it to the execution trace.
    ///
    /// # Returns
    ///
    /// Whether the operation was already successfully included (`true`), or was already present in
    /// the stash.
    ///
    /// # Nota bene
    ///
    /// It is required to call [`Self::commit_transaction`] after all calls to this method.
    pub fn apply_verify(
        &mut self,
        operation: Operation,
        force: bool,
    ) -> Result<bool, MultiError<AcceptError, S::Error>> {
        if operation.contract_id != self.contract_id() {
            return Err(MultiError::A(AcceptError::Articles(SemanticError::ContractMismatch)));
        }

        let opid = operation.opid();

        let present = self.0.is_valid(opid);
        let articles = self.0.articles();
        if !present || force {
            let verified = articles
                .codex()
                .verify(self.contract_id(), operation, &self.0.state().raw, articles)
                .map_err(AcceptError::from)
                .map_err(MultiError::A)?;
            self.apply_internal(opid, verified, present && !force)
                .map_err(MultiError::B)?;
        }

        Ok(present)
    }

    /// Adds operation which was already checked to the stock. This does the following:
    /// - includes raw operation to stash;
    /// - computes state modification and applies it to the state;
    /// - saves removed state as a [`Transition`] and adds it to the execution trace.
    ///
    /// # Returns
    ///
    /// State invalidated by the operation in the form of a [`Transition`].
    ///
    /// # Nota bene
    ///
    /// It is required to call [`Self::commit_transaction`] after all calls to this method.
    pub fn apply(&mut self, operation: VerifiedOperation) -> Result<Transition, S::Error> {
        let opid = operation.opid();
        let present = self.0.is_valid(opid);
        self.apply_internal(opid, operation, present)
    }

    fn apply_internal(
        &mut self,
        opid: Opid,
        operation: VerifiedOperation,
        present: bool,
    ) -> Result<Transition, S::Error> {
        if !present {
            self.0.add_operation(opid, operation.as_operation());
        }

        let op = operation.as_operation();
        for read in &op.immutable_in {
            self.0.add_reading(*read, opid);
        }
        for prevout in &op.destructible_in {
            self.0.add_spending(prevout.addr, opid);
        }

        let transition = self
            .0
            .update_state(|state, articles| state.apply(operation, articles.semantics()))?;

        self.0.add_transition(opid, &transition);
        self.0.mark_valid(opid);
        Ok(transition)
    }

    pub fn commit_transaction(&mut self) { self.0.commit_transaction(); }
}

/// Computes the list of operations to be exported into a consignment: the ancestor closure of
/// `seeds`, followed both over destructible and immutable inputs, in a dependency-first order
/// suitable for stream verification (a producer is always emitted before its consumers).
///
/// Operations unrelated by dependencies keep their relative order in `operations`. Genesis is not
/// a part of the stash and is never included; references to it are skipped.
///
/// # Errors
///
/// Returns [`io::ErrorKind::InvalidData`] when the stash is inconsistent and no valid consignment
/// can be produced: a seed or a referenced parent operation is absent from `operations`, an opid
/// occurs twice, or the dependency graph contains a cycle.
fn plan_export(
    operations: Vec<(Opid, Operation)>,
    genesis_opid: Opid,
    seeds: impl IntoIterator<Item = Opid>,
) -> io::Result<Vec<(Opid, Operation)>> {
    let invalid = |msg: String| io::Error::new(io::ErrorKind::InvalidData, msg);

    let mut index_by_opid = HashMap::with_capacity(operations.len());
    for (index, (opid, _)) in operations.iter().enumerate() {
        if index_by_opid.insert(*opid, index).is_some() {
            return Err(invalid(format!("duplicate operation {opid} in the contract stash")));
        }
    }

    // Ancestor closure over both input types, using operation data as the source of truth
    // (the trace may be incomplete, while inputs are commitment-verified parts of operations).
    let mut included = vec![false; operations.len()];
    let mut queue = VecDeque::new();
    for seed in seeds {
        if seed == genesis_opid {
            continue;
        }
        let &index = index_by_opid
            .get(&seed)
            .ok_or_else(|| invalid(format!("operation {seed} is missing from the contract stash")))?;
        if !included[index] {
            included[index] = true;
            queue.push_back(index);
        }
    }
    let parents = |op: &Operation| {
        op.destructible_in
            .iter()
            .map(|input| input.addr.opid)
            .chain(op.immutable_in.iter().map(|addr| addr.opid))
            .collect::<BTreeSet<_>>()
    };
    while let Some(index) = queue.pop_front() {
        let (opid, op) = &operations[index];
        for parent in parents(op) {
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
                queue.push_back(parent_index);
            }
        }
    }

    // Stable topological sort (Kahn's algorithm) over the included operations; the original
    // position is the tie-breaker, so already-ordered stashes are exported unchanged.
    let mut children = vec![Vec::new(); operations.len()];
    let mut indegrees = vec![0usize; operations.len()];
    for (index, (_, op)) in operations.iter().enumerate() {
        if !included[index] {
            continue;
        }
        for parent in parents(op) {
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
    let mut order = Vec::with_capacity(operations.len());
    while let Some(index) = ready.pop_first() {
        order.push(index);
        for &child in &children[index] {
            indegrees[child] -= 1;
            if indegrees[child] == 0 {
                ready.insert(child);
            }
        }
    }
    let included_count = included.iter().filter(|&&inc| inc).count();
    if order.len() != included_count {
        return Err(invalid(s!("contract stash contains a dependency cycle between operations")));
    }

    let mut slots = operations.into_iter().map(Some).collect::<Vec<_>>();
    Ok(order
        .into_iter()
        .map(|index| {
            slots[index]
                .take()
                .expect("topological order visits every operation once")
        })
        .collect())
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
        pub fn export_all_to_file(&self, output: impl AsRef<Path>) -> io::Result<()> {
            let file = BinFile::<DEEDS_MAGIC_NUMBER, DEEDS_VERSION>::create_new(output)?;
            let writer = StrictWriter::with(StreamWriter::new::<{ usize::MAX }>(file));
            self.export_all(writer)
        }

        pub fn export_to_file(
            &self,
            terminals: impl IntoIterator<Item = impl Borrow<AuthToken>>,
            output: impl AsRef<Path>,
        ) -> io::Result<()> {
            let file = BinFile::<DEEDS_MAGIC_NUMBER, DEEDS_VERSION>::create_new(output)?;
            let writer = StrictWriter::with(StreamWriter::new::<{ usize::MAX }>(file));
            self.export(terminals, writer)
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
    use ultrasonic::{fe256, Input, StateValue};

    use super::*;

    fn contract_id() -> ContractId { ContractId::from([0xC0; 32]) }

    /// Builds a real operation whose opid is its actual commitment id, so the test covers the
    /// dependency extraction from `destructible_in`/`immutable_in` the same way export does.
    fn make_op(nonce: u64, destructible: &[CellAddr], immutable: &[CellAddr]) -> (Opid, Operation) {
        let mut destructible_in = SmallVec::new();
        for addr in destructible {
            destructible_in
                .push(Input { addr: *addr, witness: StateValue::None })
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

    fn opids(plan: &[(Opid, Operation)]) -> Vec<Opid> { plan.iter().map(|(opid, _)| *opid).collect() }

    #[test]
    fn destructible_consumer_stored_before_producer_is_reordered() {
        let genesis = genesis();
        let (a_id, a) = make_op(1, &[CellAddr::new(genesis, 0)], &[]);
        let (b_id, b) = make_op(2, &[CellAddr::new(a_id, 0)], &[]);

        let plan = plan_export(vec![(b_id, b), (a_id, a)], genesis, [b_id]).unwrap();
        assert_eq!(opids(&plan), vec![a_id, b_id]);
    }

    #[test]
    fn immutable_consumer_stored_before_producer_is_reordered() {
        let genesis = genesis();
        let (a_id, a) = make_op(1, &[CellAddr::new(genesis, 0)], &[]);
        let (b_id, b) = make_op(2, &[CellAddr::new(genesis, 1)], &[CellAddr::new(a_id, 0)]);

        let plan = plan_export(vec![(b_id, b), (a_id, a)], genesis, [b_id]).unwrap();
        assert_eq!(opids(&plan), vec![a_id, b_id]);
    }

    #[test]
    fn multi_level_reverse_order_is_reordered() {
        let genesis = genesis();
        let (a_id, a) = make_op(1, &[CellAddr::new(genesis, 0)], &[]);
        let (b_id, b) = make_op(2, &[CellAddr::new(a_id, 0)], &[]);
        let (c_id, c) = make_op(3, &[CellAddr::new(b_id, 0)], &[CellAddr::new(a_id, 1)]);

        let plan = plan_export(vec![(c_id, c), (b_id, b), (a_id, a)], genesis, [c_id]).unwrap();
        assert_eq!(opids(&plan), vec![a_id, b_id, c_id]);
    }

    #[test]
    fn unrelated_operations_keep_stash_order() {
        let genesis = genesis();
        let (a_id, a) = make_op(1, &[CellAddr::new(genesis, 0)], &[]);
        let (b_id, b) = make_op(2, &[CellAddr::new(genesis, 1)], &[]);
        let (c_id, c) = make_op(3, &[CellAddr::new(genesis, 2)], &[]);

        let plan = plan_export(vec![(c_id, c), (a_id, a), (b_id, b)], genesis, [c_id, a_id, b_id]).unwrap();
        assert_eq!(opids(&plan), vec![c_id, a_id, b_id]);
    }

    #[test]
    fn closure_excludes_operations_outside_seed_ancestry() {
        let genesis = genesis();
        let (a_id, a) = make_op(1, &[CellAddr::new(genesis, 0)], &[]);
        let (b_id, b) = make_op(2, &[CellAddr::new(a_id, 0)], &[]);
        let (c_id, c) = make_op(3, &[CellAddr::new(genesis, 1)], &[]);

        let plan = plan_export(vec![(c_id, c), (b_id, b), (a_id, a)], genesis, [b_id]).unwrap();
        assert_eq!(opids(&plan), vec![a_id, b_id]);
    }

    #[test]
    fn seed_ancestors_are_traversed_through_both_input_types() {
        // Models a published-state seed: the seed itself is not a terminal ancestor, but its own
        // ancestors must still be exported.
        let genesis = genesis();
        let (a_id, a) = make_op(1, &[CellAddr::new(genesis, 0)], &[]);
        let (b_id, b) = make_op(2, &[], &[CellAddr::new(a_id, 0)]);

        let plan = plan_export(vec![(b_id, b), (a_id, a)], genesis, [b_id]).unwrap();
        assert_eq!(opids(&plan), vec![a_id, b_id]);
    }

    #[test]
    fn genesis_references_are_skipped() {
        let genesis = genesis();
        let (a_id, a) = make_op(1, &[CellAddr::new(genesis, 0)], &[CellAddr::new(genesis, 1)]);

        let plan = plan_export(vec![(a_id, a)], genesis, [a_id]).unwrap();
        assert_eq!(opids(&plan), vec![a_id]);
    }

    #[test]
    fn missing_parent_fails_closed() {
        let genesis = genesis();
        let (a_id, _) = make_op(1, &[CellAddr::new(genesis, 0)], &[]);
        let (b_id, b) = make_op(2, &[CellAddr::new(a_id, 0)], &[]);

        let err = plan_export(vec![(b_id, b)], genesis, [b_id]).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn missing_seed_fails_closed() {
        let genesis = genesis();
        let (a_id, a) = make_op(1, &[CellAddr::new(genesis, 0)], &[]);
        let (b_id, _) = make_op(2, &[CellAddr::new(a_id, 0)], &[]);

        let err = plan_export(vec![(a_id, a)], genesis, [b_id]).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn dependency_cycle_fails_closed() {
        // A cycle cannot occur with real commitment-derived opids; synthetic keys model a
        // corrupted stash.
        let genesis = genesis();
        let k1 = Opid::from([0x01; 32]);
        let k2 = Opid::from([0x02; 32]);
        let (_, op1) = make_op(1, &[CellAddr::new(k2, 0)], &[]);
        let (_, op2) = make_op(2, &[CellAddr::new(k1, 0)], &[]);

        let err = plan_export(vec![(k1, op1), (k2, op2)], genesis, [k1]).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn duplicate_opid_fails_closed() {
        let genesis = genesis();
        let (a_id, a) = make_op(1, &[CellAddr::new(genesis, 0)], &[]);

        let err = plan_export(vec![(a_id, a.clone()), (a_id, a)], genesis, [a_id]).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    }
}
