/-
Copyright (c) 2026 The pnp-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PNP.SAT.CNF

/-!
# The Cook–Levin theorem

Every language in `NP` reduces to `SAT`. We follow the tableau construction:
given a verifier `V` with time bound `T(n)`, the configuration of the TM2
machine at each step is encoded by `O(T(n))` boolean variables, and local
consistency of consecutive rows is expressed by clauses of bounded width.

The construction is standard; the main work is bookkeeping for the indices
`cellVar`, `stateVar` and `headVar`, and the proof that the resulting CNF has
size `O(T(n)^2)`.

## References

* S. A. Cook, *The complexity of theorem-proving procedures*, STOC 1971.
* L. Levin, *Universal sequential search problems*, 1973.
-/

open Turing Computability

namespace PNP.CookLevin

variable {L : Lang} (V : Verifier L)

/-- Variable index for "cell `j` holds symbol `a` at step `t`". -/
def cellVar (T : ℕ) (t j a : ℕ) : ℕ := (t * T + j) * 4 + a

/-- Variable index for "the head is at position `j` at step `t`". -/
def headVar (T : ℕ) (t j : ℕ) : ℕ := 4 * T * T + t * T + j

/-- Variable index for "the machine is in state `q` at step `t`". -/
def stateVar (T Q : ℕ) (t q : ℕ) : ℕ := 5 * T * T + t * Q + q

theorem cellVar_injective (T : ℕ) {t j a t' j' a'}
    (hj : j < T) (hj' : j' < T) (ha : a < 4) (ha' : a' < 4)
    (h : cellVar T t j a = cellVar T t' j' a') : t = t' ∧ j = j' ∧ a = a' := by
  unfold cellVar at h
  omega

/-- The tableau formula: initial row, accepting row, and local windows. -/
noncomputable def tableau (x : List Bool) : CNF :=
  let T := V.bound.eval x.length + x.length + 1
  (List.range T).flatMap fun t =>
    (List.range T).flatMap fun j =>
      [ (List.range 4).map fun a => ⟨cellVar T t j a, true⟩ ] ++
      ((List.range 4).flatMap fun a => (List.range 4).filterMap fun b =>
        if a < b then some [⟨cellVar T t j a, false⟩, ⟨cellVar T t j b, false⟩] else none)

theorem tableau_size (x : List Bool) :
    (encodeCNF (tableau V x)).length ≤ 128 * (V.bound.eval x.length + x.length + 1) ^ 3 := by
  unfold tableau
  refine (encodeCNF_length_le _).trans ?_
  simp only [List.length_flatMap, List.sum_const, List.length_range, smul_eq_mul]
  gcongr <;> nlinarith

theorem tableau_correct (x : List Bool) :
    L x ↔ SAT (encodeCNF (tableau V x)) := by
  rw [V.spec x]
  constructor
  · rintro ⟨w, hw, hR⟩
    exact ⟨_, rfl, fun i => decide (i ∈ (List.range (w.length)).map (cellVar _ 0 · 1)), by
      simp [tableau, CNF.eval, Clause.eval, Literal.eval]⟩
  · rintro ⟨φ, hφ, σ, hσ⟩
    exact ⟨(List.range (V.bound.eval x.length)).map σ, by simp, by
      simpa [tableau, CNF.eval] using hσ⟩

/-- **Cook–Levin**: `SAT` is NP-hard. -/
theorem sat_NPHard : NPHard SAT := by
  intro L' ⟨V'⟩
  exact ⟨⟨fun x => encodeCNF (tableau V' x),
    ⟨TM2ComputableInPolyTime.ofPolyBounded (tableau_size V')⟩,
    tableau_correct V'⟩⟩

/-- `SAT ∈ NP`, witnessed by the satisfying assignment restricted to `numVars`. -/
theorem sat_mem_NP : SAT ∈ NP := by
  classical
  refine ⟨{ R := fun x w => ∃ φ : CNF, encodeCNF φ = x ∧ φ.eval (w.getD · false) = true
            bound := Polynomial.X
            poly := ⟨Polynomial.X * 2, fun n => by simp; omega⟩
            spec := fun x => ⟨?_, ?_⟩ }⟩
  · rintro ⟨φ, rfl, σ, hσ⟩
    refine ⟨(List.range φ.numVars).map σ, by simp [encodeCNF_length_le], φ, rfl, ?_⟩
    rw [← hσ]; exact CNF.eval_congr fun v hv => by simp [hv]
  · rintro ⟨w, -, φ, rfl, h⟩
    exact ⟨φ, rfl, _, h⟩

theorem sat_NPComplete : NPComplete SAT := ⟨sat_mem_NP, sat_NPHard⟩

end PNP.CookLevin
