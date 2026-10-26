# Lean environment setup

## Use

```bash
cd /data/hrm/lean_workspace
source env.sh
lean --version
lake env lean Smoke.lean
```

`env.sh` selects `/data/hrm/elan` and keeps temporary files and caches on `/data`.
It must be sourced in each new shell. No global shell startup files were changed.

## Versions and provenance

- elan: Ubuntu package 3.1.0 (`/usr/bin/elan`).
- Lean: 4.28.0, commit 7e01a1bf5c70fc6167d49c345d3bf80596e9a79b.
- Official Linux archive SHA-256: `ceb3a3f844f7aebf63245e2b51c28d5b0ed38942c19f93cf3febd520302160bd` (verified).
- FATE-X: `a6fb49ee85fd05bb8ce9fc66e1c66797b5a0592d`, extracted under `vendor/fatex-source`.
- Mathlib: v4.28.0, `8f9d9cff6bd728b17a24e163c9402775d9e6a365`, under `vendor/mathlib-source`.
- Other dependency archives use the exact commits in the original FATE-X manifest.

Git cloning timed out, so dependencies were downloaded as official GitHub commit archives.
The root Lake project uses local path dependencies; the original Mathlib manifest is unchanged.
Mathlib cache extraction writes non-Mathlib artifacts into `.lake/packages`, so those build
artifacts were also copied into the local path dependencies' `.lake/build` directories.
Repeat that copy after fetching a new cache if necessary.
ProofWidgets has local synthetic Git metadata solely for release-tag lookup; its local HEAD
is NOT the upstream commit. Its source came from the pinned commit archive.
Mathlib has an initialized Git directory with an upstream origin for cache repository detection;
this is NOT a full Git checkout either.

## Verification completed

- Official Lean archive checksum verified.
- `lean --version` and `lake --version` succeeded.
- All 8,010 cache downloads completed and were decompressed.
- `lake env lean Smoke.lean` succeeded twice (~6 seconds each), including `import Mathlib`,
  `simp`, `ring`, and `norm_num`; no sorry in this file.
- FATE-X files `FATEX/1.lean` and `FATEX/100.lean` elaborate successfully with their expected
  `declaration uses sorry` warnings. These are statement compatibility checks, NOT solved tasks.
- The other 98 benchmark files have not yet been checked.

The MAESTRO implementation itself is described in README.md and docs/paper-mapping.md.
