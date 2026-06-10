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

use core::error::Error;

use amplify::MultiError;
use sonicapi::SemanticError;
use ultrasonic::{CallError, CellAddr, ContractName, Operation, Opid};

use crate::{Articles, EffectiveState, Transition};

/// A session encapsulates all I/O access to a [`Stock`].
///
/// Callers open one session per logical operation and forward it through the call chain, ensuring
/// that the underlying I/O resource (e.g. a database connection) is acquired exactly once.
///
/// For lock-free backends (e.g. file-system) the session is simply `&'s mut Self`.
pub trait StockSession {
    type Error: Error;

    // ── read ──────────────────────────────────────────────────────────────

    fn is_valid(&mut self, opid: Opid) -> bool;
    fn has_operation(&mut self, opid: Opid) -> bool;
    fn operation_count(&mut self) -> u64;
    fn operation(&mut self, opid: Opid) -> Operation;
    fn operations(&mut self) -> impl Iterator<Item = (Opid, Operation)>;
    fn valid_opids(&mut self) -> impl Iterator<Item = Opid> {
        let opids = self
            .operations()
            .map(|(opid, _)| opid)
            .collect::<Vec<_>>();
        let valid = opids
            .into_iter()
            .filter(|opid| self.is_valid(*opid))
            .collect::<Vec<_>>();
        valid.into_iter()
    }
    fn operation_parent_ops(&mut self) -> impl Iterator<Item = (Opid, Vec<Opid>)> {
        self.operations()
            .map(|(opid, op)| {
                let parents = op
                    .immutable_in
                    .iter()
                    .map(|inp| inp.opid)
                    .chain(op.destructible_in.iter().map(|inp| inp.addr.opid))
                    .collect();
                (opid, parents)
            })
    }
    fn transition(&mut self, opid: Opid) -> Transition;
    fn trace(&mut self) -> impl Iterator<Item = (Opid, Transition)>;
    fn read_by(&mut self, addr: CellAddr) -> impl Iterator<Item = Opid>;
    fn spent_by(&mut self, addr: CellAddr) -> Option<Opid>;

    // ── write ─────────────────────────────────────────────────────────────

    fn mark_valid(&mut self, opid: Opid);
    fn mark_invalid(&mut self, opid: Opid);

    fn update_articles(
        &mut self,
        f: impl FnOnce(&mut Articles) -> Result<bool, SemanticError>,
    ) -> Result<bool, MultiError<SemanticError, Self::Error>>;

    fn update_state<R>(&mut self, f: impl FnOnce(&mut EffectiveState, &Articles) -> R) -> Result<R, Self::Error>;

    fn add_operation(&mut self, opid: Opid, operation: &Operation);
    fn add_transition(&mut self, opid: Opid, transition: &Transition);
    fn add_reading(&mut self, addr: CellAddr, reader: Opid);
    fn add_spending(&mut self, spent: CellAddr, spender: Opid);
    fn commit_transaction(&mut self) -> Result<(), Self::Error>;
}

/// Stock is a persistence API for keeping and accessing contract data.
pub trait Stock {
    type Conf;
    type Error: Error;

    /// Session type for all I/O access.
    /// For lock-free backends: `type Session<'s> = &'s mut Self`.
    type Session<'s>: StockSession<Error = Self::Error>
    where Self: 's;

    fn new(articles: Articles, state: EffectiveState, conf: Self::Conf) -> Result<Self, Self::Error>
    where Self: Sized;

    fn load(conf: Self::Conf) -> Result<Self, Self::Error>
    where Self: Sized;

    fn config(&self) -> Self::Conf;

    /// In-memory, non-blocking.
    fn articles(&self) -> &Articles;

    /// In-memory, non-blocking.
    fn state(&self) -> &EffectiveState;

    /// Opens a session for all I/O operations.
    fn session(&mut self) -> Self::Session<'_>;
}

#[derive(Clone, PartialEq, Eq, Debug, Display, Error)]
#[display(doc_comments)]
pub enum IssueError {
    /// unable to issue a new contract '{0}' due to invalid genesis data. Specifically, {1}
    Genesis(ContractName, CallError),
}
