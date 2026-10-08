# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.5.0](https://github.com/HellButcher/tinybox-rs/compare/v0.4.1...v0.5.0) - 2026-10-08

### Fixed

- allow coercion in unstable

### Other

- document public items

## [0.4.1](https://github.com/HellButcher/tinybox-rs/compare/v0.4.0...v0.4.1) - 2026-10-05

### Fixed

- make test with miri green, even without unstable feature

### Other

- also test miri without unstable feature
- add miri test

## [0.4.0](https://github.com/HellButcher/tinybox-rs/compare/v0.3.1...v0.4.0) - 2026-10-04

### Fixed

- reduced UB
- use Layout::for_value_raw to avoid creating dangeling references

### Other

- update pipeline
- automatic clippy fixes
- update github actions
- use sparse crates.io index
- update README.md
