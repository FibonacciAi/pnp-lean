import Lake
open Lake DSL

package pnp where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

@[default_target]
lean_lib PNP where
  globs := #[.submodules `PNP]

/-- `lake exe verify` : kernel-check `PNP.P_eq_NP` against the prebuilt oleans
and replay the certificate trace (see `scripts/`). -/
lean_exe verify where
  root := `Verify.Main
  supportInterpreter := true
