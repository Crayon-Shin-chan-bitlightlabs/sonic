// SONIC: Standard library for formally-verifiable distributed contracts
//
// SPDX-License-Identifier: Apache-2.0

use std::convert::Infallible;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::{fs, io};

use amplify::MultiError;
use aora::file::{FileAoraIndex, FileAoraMap, FileAuraMap};
use aora::{AoraIndex, AoraMap, AuraMap, TransactionalMap};
use binfile::BinFile;
use hypersonic::{
    Articles, CellAddr, EffectiveState, Genesis, Issue, IssueError, Ledger, Operation, Opid, RawState, SemanticError,
    Semantics, SigBlob, Stock, StockSession, Transition,
};
use strict_encoding::{DecodeError, StreamReader, StreamWriter, StrictDecode, StrictEncode, StrictWriter};

#[derive(Wrapper, WrapperMut, Debug, From)]
#[wrapper(Deref)]
#[wrapper_mut(DerefMut)]
pub struct LedgerDir(Ledger<StockFs>);

const STASH_MAGIC: u64 = u64::from_be_bytes(*b"CONSTASH");
const TRACE_MAGIC: u64 = u64::from_be_bytes(*b"CONTRACE");
const SPENT_MAGIC: u64 = u64::from_be_bytes(*b"OPSPENT ");
const READ_MAGIC: u64 = u64::from_be_bytes(*b"OPREADBY");
const VALID_MAGIC: u64 = u64::from_be_bytes(*b"OPVALID ");
const SEMANTICS_MAGIC: u64 = u64::from_be_bytes(*b"SEMANTIC");
const STATE_MAGIC: u64 = u64::from_be_bytes(*b"CONSTATE");
const GENESIS_MAGIC: u64 = u64::from_be_bytes(*b"CGENESIS");
const PERSISTENCE_VERSION_0: u16 = 0;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum OpValidity {
    Invalid,
    Valid,
}

impl From<[u8; 1]> for OpValidity {
    fn from(b: [u8; 1]) -> Self {
        if b[0] == 1 {
            Self::Valid
        } else {
            Self::Invalid
        }
    }
}
impl From<OpValidity> for [u8; 1] {
    fn from(v: OpValidity) -> Self {
        if v == OpValidity::Valid {
            [1]
        } else {
            [0]
        }
    }
}
impl From<OpValidity> for bool {
    fn from(v: OpValidity) -> Self { v == OpValidity::Valid }
}

#[derive(Debug)]
pub struct StockFs {
    path: PathBuf,
    stash: FileAoraMap<Opid, Operation, STASH_MAGIC, 1>,
    trace: FileAoraMap<Opid, Transition, TRACE_MAGIC, 1>,
    valid: FileAuraMap<Opid, OpValidity, VALID_MAGIC, 1, 32, 1>,
    spent: FileAuraMap<CellAddr, Opid, SPENT_MAGIC, 1, 34>,
    read: FileAoraIndex<CellAddr, Opid, READ_MAGIC, 1, 34>,
    articles: Articles,
    state: EffectiveState,
}

impl StockFs {
    const FILENAME_CODEX: &'static str = "codex.yaml";
    const FILENAME_META: &'static str = "meta.toml";
    const FILENAME_GENESIS: &'static str = "genesis.dat";
    const FILENAME_SEMANTICS: &'static str = "semantics.dat";
    const FILENAME_STATE_RAW: &'static str = "state.dat";
}

/// For the FS backend, the session IS `&mut StockFs` — zero overhead.
impl StockSession for &mut StockFs {
    type Error = FsError;

    // ── read ──────────────────────────────────────────────────────────────
    fn is_valid(&mut self, opid: Opid) -> bool { self.valid.get(opid).map(bool::from).unwrap_or_default() }
    fn has_operation(&mut self, opid: Opid) -> bool { self.stash.contains_key(opid) }
    fn operation_count(&mut self) -> u64 { self.stash.len() as u64 }
    fn operation(&mut self, opid: Opid) -> Operation { self.stash.get_expect(opid) }
    fn operations(&mut self) -> impl Iterator<Item = (Opid, Operation)> { self.stash.iter() }
    fn transition(&mut self, opid: Opid) -> Transition { self.trace.get_expect(opid) }
    fn trace(&mut self) -> impl Iterator<Item = (Opid, Transition)> { self.trace.iter() }
    fn read_by(&mut self, addr: CellAddr) -> impl Iterator<Item = Opid> { self.read.get(addr) }
    fn spent_by(&mut self, addr: CellAddr) -> Option<Opid> { self.spent.get(addr) }

    // ── write ─────────────────────────────────────────────────────────────
    fn mark_valid(&mut self, opid: Opid) { self.valid.insert_or_update(opid, OpValidity::Valid) }
    fn mark_invalid(&mut self, opid: Opid) { self.valid.insert_or_update(opid, OpValidity::Invalid) }

    fn update_articles(
        &mut self,
        f: impl FnOnce(&mut Articles) -> Result<bool, SemanticError>,
    ) -> Result<bool, MultiError<SemanticError, FsError>> {
        let res = f(&mut self.articles).map_err(MultiError::A)?;
        let file =
            BinFile::<SEMANTICS_MAGIC, PERSISTENCE_VERSION_0>::create(self.path.join(StockFs::FILENAME_SEMANTICS))
                .map_err(MultiError::from_b)?;
        let mut w = StreamWriter::new::<{ usize::MAX }>(file);
        self.articles
            .semantics()
            .strict_write(&mut w)
            .map_err(MultiError::from_b)?;
        self.articles
            .sig()
            .strict_write(w)
            .map_err(MultiError::from_b)?;
        Ok(res)
    }

    fn update_state<R>(&mut self, f: impl FnOnce(&mut EffectiveState, &Articles) -> R) -> Result<R, FsError> {
        let res = f(&mut self.state, &self.articles);
        let file = BinFile::<STATE_MAGIC, PERSISTENCE_VERSION_0>::create(self.path.join(StockFs::FILENAME_STATE_RAW))?;
        self.state
            .raw
            .strict_write(StreamWriter::new::<{ usize::MAX }>(file))?;
        self.state.recompute(self.articles.semantics());
        Ok(res)
    }

    fn add_operation(&mut self, opid: Opid, op: &Operation) { self.stash.insert(opid, op) }
    fn add_transition(&mut self, opid: Opid, t: &Transition) { self.trace.insert(opid, t) }
    fn add_reading(&mut self, addr: CellAddr, reader: Opid) { self.read.push(addr, reader) }
    fn add_spending(&mut self, spent: CellAddr, spender: Opid) { self.spent.insert_or_update(spent, spender) }

    fn commit_transaction(&mut self) -> Result<(), FsError> {
        self.spent.commit_transaction();
        self.valid.commit_transaction();
        Ok(())
    }
}

impl Stock for StockFs {
    type Conf = PathBuf;
    type Error = FsError;
    type Session<'s> = &'s mut Self;

    fn new(articles: Articles, state: EffectiveState, path: PathBuf) -> Result<Self, FsError> {
        let stash = FileAoraMap::create_new(&path, "stash")?;
        let trace = FileAoraMap::create_new(&path, "trace")?;
        let spent = FileAuraMap::create_new(&path, "spent")?;
        let read = FileAoraIndex::create_new(&path, "read")?;
        let valid = FileAuraMap::create_new(&path, "valid")?;

        let meta = toml::to_string(&articles.issue().meta)?;
        let mut f = File::create_new(path.join(Self::FILENAME_META))?;
        f.write_all(meta.as_ref())?;
        serde_yaml::to_writer(File::create_new(path.join(Self::FILENAME_CODEX))?, articles.codex())?;

        articles
            .genesis()
            .strict_write(StreamWriter::new::<{ usize::MAX }>(
                BinFile::<GENESIS_MAGIC, PERSISTENCE_VERSION_0>::create_new(path.join(Self::FILENAME_GENESIS))?,
            ))?;
        let mut w = StreamWriter::new::<{ usize::MAX }>(BinFile::<SEMANTICS_MAGIC, PERSISTENCE_VERSION_0>::create_new(
            path.join(Self::FILENAME_SEMANTICS),
        )?);
        articles.semantics().strict_write(&mut w)?;
        articles.sig().strict_write(w)?;
        state.raw.strict_write(StreamWriter::new::<{ usize::MAX }>(
            BinFile::<STATE_MAGIC, PERSISTENCE_VERSION_0>::create_new(path.join(Self::FILENAME_STATE_RAW))?,
        ))?;
        Ok(Self { path, stash, trace, spent, read, articles, state, valid })
    }

    fn load(path: PathBuf) -> Result<Self, FsError> {
        let stash = FileAoraMap::open(&path, "stash")?;
        let trace = FileAoraMap::open(&path, "trace")?;
        let spent = FileAuraMap::open(&path, "spent")?;
        let read = FileAoraIndex::open(&path, "read")?;
        let valid = FileAuraMap::open(&path, "valid")?;
        let meta = toml::from_str(&fs::read_to_string(path.join(Self::FILENAME_META))?)?;
        let codex = serde_yaml::from_reader(File::open(path.join(Self::FILENAME_CODEX))?)?;
        let genesis =
            Genesis::strict_read(StreamReader::new::<{ usize::MAX }>(
                BinFile::<GENESIS_MAGIC, PERSISTENCE_VERSION_0>::open(path.join(Self::FILENAME_GENESIS))?,
            ))?;
        let mut r = StreamReader::new::<{ usize::MAX }>(BinFile::<SEMANTICS_MAGIC, PERSISTENCE_VERSION_0>::open(
            path.join(Self::FILENAME_SEMANTICS),
        )?);
        let semantics = Semantics::strict_read(&mut r)?;
        let sig = Option::<SigBlob>::strict_read(r)?;
        let raw =
            RawState::strict_read(StreamReader::new::<{ usize::MAX }>(
                BinFile::<STATE_MAGIC, PERSISTENCE_VERSION_0>::open(path.join(Self::FILENAME_STATE_RAW))?,
            ))?;
        let issue = Issue { version: default!(), meta, codex, genesis };
        let articles = Articles::with(semantics, issue, sig, |_, _, _| -> Result<_, Infallible> { Ok(()) })?;
        let state = EffectiveState::with_raw_state(raw, &articles);
        Ok(Self { path, stash, trace, spent, read, articles, state, valid })
    }

    fn config(&self) -> PathBuf { self.path.clone() }
    fn articles(&self) -> &Articles { &self.articles }
    fn state(&self) -> &EffectiveState { &self.state }
    fn session(&mut self) -> &mut Self { self }
}

impl LedgerDir {
    pub fn new(articles: Articles, conf: PathBuf) -> Result<Self, MultiError<IssueError, FsError>> {
        Ledger::new(articles, conf).map(Self)
    }
    pub fn load(conf: PathBuf) -> Result<Self, FsError> { Ledger::load(conf).map(Self) }
    pub fn backup_to_file(&mut self, output: impl AsRef<Path>) -> io::Result<()> {
        let file = File::create_new(output)?;
        self.export_all(StrictWriter::with(StreamWriter::new::<{ usize::MAX }>(file)))
    }
    pub fn path(&self) -> &Path { &self.0.stock().path }
}

#[derive(Debug, Display, Error, From)]
#[display(inner)]
pub enum FsError {
    #[from]
    Io(io::Error),
    #[from]
    Decode(DecodeError),
    #[from]
    Articles(SemanticError),
    #[from]
    Yaml(serde_yaml::Error),
    #[from]
    TomlDecode(toml::de::Error),
    #[from]
    TomlEncode(toml::ser::Error),
}
