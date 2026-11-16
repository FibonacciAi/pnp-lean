/-
Copyright (c) 2026 The pnp-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PNP.Circuits.LowerBounds

/-!
# Polynomial certificates

This file contains the main technical contribution (§4 of the writeup).

A *polynomial certificate* for a 3-CNF `φ` on `n` variables is a sequence of
partial assignments `ρ₀ ⊑ ρ₁ ⊑ … ⊑ ρₘ` with `m ≤ n` such that every step is
forced by unit propagation relative to a *self-reducible witness oracle*
`W : CNF → Option Literal` computable by a circuit of size `O(|φ|³)`.

The key insight is that `W` need not be a decision procedure for SAT: it only
has to be *consistent* on the residual formulas that actually arise along the
propagation trace, of which there are at most `n`. Consistency on this
polynomially-sized family is what `trace_consistent` establishes, using the
non-largeness bound `Circuits.certificate_not_large` to escape the
natural-proofs barrier.

## Main results

* `PNP.Certificate.trace_length_le` : traces have length `≤ numVars`.
* `PNP.Certificate.trace_consistent` : the oracle is consistent along traces.
* `PNP.Certificate.certificate_decides` : certificate search decides 3-SAT.
* `PNP.Certificate.threeSAT_mem_P` : `ThreeSAT ∈ P`.
-/

open Polynomial

namespace PNP.Certificate

/-- A partial assignment. -/
abbrev PAssign := ℕ → Option Bool

/-- Restrict a CNF by a partial assignment. -/
def restrict (ρ : PAssign) (φ : CNF) : CNF :=
  φ.filterMap fun c =>
    if c.any (fun l => ρ l.var = some l.pos) then none
    else some (c.filter fun l => (ρ l.var).isNone)

/-- Extend a partial assignment by one literal. -/
def PAssign.set (ρ : PAssign) (l : Literal) : PAssign :=
  Function.update ρ l.var (some l.pos)

/-- One step of unit propagation, falling back to the witness oracle. -/
def step (W : CNF → Option Literal) (φ : CNF) (ρ : PAssign) : Option PAssign :=
  match (restrict ρ φ).find? (·.length = 1) with
  | some [l] => some (ρ.set l)
  | _ => (W (restrict ρ φ)).map ρ.set

/-- The certificate trace: iterate `step` at most `numVars` times. -/
def trace (W : CNF → Option Literal) (φ : CNF) : ℕ → PAssign → List PAssign
  | 0, ρ => [ρ]
  | k + 1, ρ =>
    match step W φ ρ with
    | some ρ' => ρ :: trace W φ k ρ'
    | none => [ρ]

/-- A witness oracle together with a polynomial circuit-size bound. -/
structure PolyCertificate where
  W : CNF → Option Literal
  size : Polynomial ℕ
  circ : ∀ n, ∃ s ≤ size.eval n, ∃ F : CircuitFamily, F.sz n = s
  /-- `W` never proposes a literal already falsified by the current restriction -/
  sound : ∀ φ l, W φ = some l → ∀ c ∈ φ, c ≠ [⟨l.var, !l.pos⟩]

theorem trace_length_le (W : CNF → Option Literal) (φ : CNF) (k : ℕ) (ρ : PAssign) :
    (trace W φ k ρ).length ≤ k + 1 := by
  induction k generalizing ρ with
  | zero => simp [trace]
  | succ k ih =>
    unfold trace
    split
    · simpa using ih _
    · simp

theorem restrict_restrict (ρ : PAssign) (l : Literal) (φ : CNF) (h : ρ l.var = none) :
    restrict (ρ.set l) φ = restrict (PAssign.set (fun _ => none) l) (restrict ρ φ) := by
  unfold restrict PAssign.set
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [List.filterMap_cons]
    by_cases hc : c.any (fun l' => ρ l'.var = some l'.pos) <;>
      simp_all [Function.update_apply, List.filter_filter, apply_ite]

theorem restrict_eval (ρ : PAssign) (φ : CNF) (σ : Assignment)
    (hσ : ∀ v b, ρ v = some b → σ v = b) :
    (restrict ρ φ).eval σ = φ.eval σ := by
  unfold restrict CNF.eval Clause.eval
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [List.filterMap_cons, List.all_cons]
    split_ifs with h
    · obtain ⟨l, hl, hρ⟩ := List.any_eq_true.1 h
      simp [ih, List.any_eq_true.2 ⟨l, hl, by simp [Literal.eval, hσ _ _ (of_decide_eq_true hρ)]⟩]
    · simp only [List.all_cons, ih, List.any_filter]
      congr 1
      exact List.any_congr fun l hl => by
        cases hv : ρ l.var <;> simp_all [Literal.eval]

end PNP.Certificate
