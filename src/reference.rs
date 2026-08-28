use std::fmt;
use std::str::FromStr;

use anyhow::{Context, Result, ensure};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ReferenceKind {
    Workspace,
    Check,
    Sync,
    Submission,
    Query,
    Issue,
    Event,
}

impl ReferenceKind {
    pub(crate) const fn prefix(self) -> char {
        match self {
            Self::Workspace => 'w',
            Self::Check => 'c',
            Self::Sync => 'u',
            Self::Submission => 's',
            Self::Query => 'q',
            Self::Issue => 'i',
            Self::Event => 'e',
        }
    }

    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::Workspace => "workspace",
            Self::Check => "check",
            Self::Sync => "sync",
            Self::Submission => "submission",
            Self::Query => "query",
            Self::Issue => "issue",
            Self::Event => "telemetry",
        }
    }

    fn from_prefix(prefix: char) -> Option<Self> {
        match prefix {
            'w' => Some(Self::Workspace),
            'c' => Some(Self::Check),
            'u' => Some(Self::Sync),
            's' => Some(Self::Submission),
            'q' => Some(Self::Query),
            'i' => Some(Self::Issue),
            'e' => Some(Self::Event),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Reference {
    kind: ReferenceKind,
    sequence: u64,
}

impl Reference {
    pub(crate) const fn new(kind: ReferenceKind, sequence: u64) -> Self {
        Self { kind, sequence }
    }

    pub(crate) const fn kind(self) -> ReferenceKind {
        self.kind
    }

    pub(crate) const fn sequence(self) -> u64 {
        self.sequence
    }

    pub(crate) fn parse_kind(value: &str, expected: ReferenceKind) -> Result<Self> {
        let reference = value
            .parse::<Self>()
            .with_context(|| format!("malformed {} reference {value}", expected.label()))?;
        ensure!(
            reference.kind == expected,
            "malformed {} reference {value}",
            expected.label()
        );
        Ok(reference)
    }

    pub(crate) fn is_kind(value: &str, expected: ReferenceKind) -> bool {
        Self::parse_kind(value, expected).is_ok()
    }
}

impl FromStr for Reference {
    type Err = anyhow::Error;

    fn from_str(value: &str) -> Result<Self> {
        let mut characters = value.chars();
        let prefix = characters.next().context("empty reference")?;
        let kind = ReferenceKind::from_prefix(prefix)
            .with_context(|| format!("unknown reference type {prefix}"))?;
        let sequence = characters.as_str();
        ensure!(
            !sequence.is_empty() && sequence.chars().all(|value| value.is_ascii_digit()),
            "malformed reference {value}"
        );
        Ok(Self::new(kind, sequence.parse()?))
    }
}

impl fmt::Display for Reference {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}{}", self.kind.prefix(), self.sequence)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn references_are_typed_and_round_trip() {
        let reference: Reference = "q42".parse().unwrap();
        assert_eq!(reference.kind(), ReferenceKind::Query);
        assert_eq!(reference.sequence(), 42);
        assert_eq!(reference.to_string(), "q42");
        assert!(Reference::parse_kind("q42", ReferenceKind::Check).is_err());
        assert!("q".parse::<Reference>().is_err());
        assert!("x1".parse::<Reference>().is_err());
    }
}
