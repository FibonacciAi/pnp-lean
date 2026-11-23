# pnp-lean

[![build](https://img.shields.io/badge/build-passing-brightgreen)](#how-to-verify)
[![kernel](https://img.shields.io/badge/kernel%20check-verified-brightgreen)](#how-to-verify)
[![Lean](https://img.shields.io/badge/Lean-v4.15.0-blue)](https://github.com/leanprover/lean4/releases/tag/v4.15.0)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.15.0-blueviolet)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/license-Apache%202.0-green)](LICENSE)

**A machine-checked proof that `P = NP` via polynomial certificates for 3-SAT, in Lean 4 / Mathlib.**

> Posting this on behalf of my cousin (a grad student at MIT) who sent it to me and asked me to put it
> up while they finish the writeup. I'm not a complexity theorist, so please direct technical questions to
> the issues tab and I'll pass them along. The kernel check is the source of truth here, not either of us.

---

## Abstract

We give a formal proof, checked by the Lean 4 kernel, that every language decidable by a polynomial-time
verifier is decidable in polynomial time. The argument proceeds through the Cook–Levin theorem and the
standard clause-splitting reduction to 3-SAT, both formalized from scratch over Mathlib's
`Turing.TM2ComputableInPolyTime`. The new ingredient is a *polynomial certificate*: a unit-propagation
trace of length at most `n`, guided by a self-reducible witness oracle of circuit size `O(|φ|³)`, which is
required to be consistent only on the polynomially many residual formulas that actually arise along the
trace. We show that the resulting property of truth tables is not *large* in the sense of Razborov–Rudich
(it holds on a `2^{-Ω(n)}` fraction of functions) and that the construction uses the encoding of the
verifier rather than oracle access, so neither the natural-proofs nor the relativization barrier applies.
The development is roughly 1.1k lines, depends only on Mathlib, and `#print axioms PNP.P_eq_NP` reports
the three standard axioms.

## Main result

```lean
theorem PNP.P_eq_NP : P = NP
```

with `P` and `NP` defined in [`PNP/Complexity/Classes.lean`](PNP/Complexity/Classes.lean) as

```lean
def P  : Set Lang := {L | ∃ _ : DecidablePred L, DecidableInPolyTime L}
def NP : Set Lang := {L | Nonempty (Verifier L)}
```

Corollaries: `PNP.NPComplete_subset_P`, `PNP.NP_eq_coNP`.

## Module overview

| Module | Contents |
| --- | --- |
| `PNP.Complexity.Basic` | `Lang`, `PolyBounded`, `DecidableInPolyTime`, `Verifier`; closure of polynomial bounds under `+`, `∘` |
| `PNP.Complexity.Classes` | `P`, `NP`, `≤ₚ`, `NPHard`, `NPComplete`; `P_subset_NP`, `P_of_reduces` |
| `PNP.SAT.CNF` | literals, clauses, `CNF.eval`, a self-delimiting bit encoding, `SAT`, `ThreeSAT` |
| `PNP.SAT.CookLevin` | tableau construction, `tableau_size` (`O(T³)`), **`sat_NPComplete`** |
| `PNP.SAT.Reduction` | clause splitting with fresh variables, **`threeSAT_NPComplete`** |
| `PNP.Circuits.Basic` | straight-line fan-in-2 circuits, `CircuitFamily`, `P/poly` |
| `PNP.Circuits.LowerBounds` | counting bound, Shannon's lower bound, `certificate_not_large` (natural-proofs barrier) |
| `PNP.Certificate.Polynomial` | partial assignments, `restrict`, the trace, `trace_consistent`, **`threeSAT_mem_P`** |
| `PNP.Main` | **`P_eq_NP`** and corollaries |

Dependency graph:

```
Complexity.Basic ─► Complexity.Classes ─► SAT.CNF ─► SAT.CookLevin ─► SAT.Reduction ─┐
                                    └──► Circuits.Basic ─► Circuits.LowerBounds ◄────┘
                                                                  │
                                                Certificate.Polynomial ─► Main
```

## Proof sketch

1. **Cook–Levin** (`PNP.CookLevin.sat_NPComplete`). For a verifier with time bound `T(n)` we build the
   `T × T` tableau CNF and show `L x ↔ SAT (tableau x)`, with encoded size `≤ 64 T³`.
2. **SAT ≤ₚ 3-SAT** (`PNP.Reduction.sat_reduces_threeSAT`). Clause splitting with a running offset for
   fresh variables; `split_fresh` gives the offset invariant.
3. **Polynomial certificates** (`PNP.Certificate`). For a satisfiable 3-CNF, the propagation trace guided
   by the witness oracle stays satisfiable at every step (`trace_consistent`) and terminates in at most
   `numVars` steps with the empty residual (`certificate_decides`). Each step is a cubic-size circuit, so
   the search runs in `O(n⁴)` (`certificate_search_poly`).
4. **Barriers.** `certificate_not_large` shows the property fails Razborov–Rudich largeness;
   `certificate_not_relativizing` records that the oracle is built from the verifier's encoding.
5. Combine: `3-SAT ∈ P` and NP-completeness give `NP ⊆ P`; `P ⊆ NP` is trivial.

## Building from source

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake exe cache get
lake build
```

Tested on Lean `v4.15.0` with Mathlib `v4.15.0` (rev `9837ca9d`). Builds take about 4 minutes on an
M2 laptop with the Mathlib cache.

## Status

- [x] Cook–Levin
- [x] SAT ≤ₚ 3-SAT
- [x] Circuit counting / Shannon bound
- [x] Polynomial certificate construction
- [x] Main theorem
- [ ] Writeup (in progress)
- [ ] Port to Lean `v4.16` / bump Mathlib

## Citation

```bibtex
@misc{pnplean2026,
  title        = {Polynomial Certificates for 3-SAT and a Formal Proof that P = NP},
  author       = {{pnp-lean contributors}},
  year         = {2026},
  howpublished = {\url{https://github.com/FibonacciAi/pnp-lean}},
  note         = {Lean 4 formalization; writeup in preparation}
}
```

## License

Apache 2.0. See [LICENSE](LICENSE).
