/-
Copyright (c) 2026 The pnp-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! Thin driver: delegates to `verify.sh`, which checks the toolchain, replays
`#print axioms PNP.P_eq_NP` against cached oleans, and renders the certificate
trace. Kept dependency-free so it builds without Mathlib. -/

def main (args : List String) : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := "./verify.sh", args := args.toArray,
    stdin := .inherit, stdout := .inherit, stderr := .inherit }
  child.wait
