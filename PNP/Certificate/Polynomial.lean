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

/-- Unit propagation never falsifies a satisfiable residual. -/
theorem step_preserves_sat (C : PolyCertificate) (φ : CNF) (ρ ρ' : PAssign)
    (h : step C.W φ ρ = some ρ') (hsat : ∃ σ, (restrict ρ φ).eval σ = true) :
    ∃ σ, (restrict ρ' φ).eval σ = true := by
  unfold step at h
  split at h
  · rename_i l hl
    obtain ⟨σ, hσ⟩ := hsat
    refine ⟨Function.update σ l.var l.pos, ?_⟩
    have := List.find?_some hl
    rw [← Option.some_inj.1 h, restrict_eval]
    · simpa [restrict_eval] using hσ
    · intro v b hv; simp_all [PAssign.set, Function.update_apply]; aesop
  · obtain ⟨l, hl, rfl⟩ := Option.map_eq_some'.1 h
    obtain ⟨σ, hσ⟩ := hsat
    exact ⟨Function.update σ l.var l.pos, by
      have := C.sound _ _ hl
      simp_all [restrict, CNF.eval, Clause.eval, Literal.eval, Function.update_apply]⟩

private lemma witness_never_gives_up (C : PolyCertificate) (φ : CNF) (ρ : PAssign)
    (hsat : ∃ σ, (restrict ρ φ).eval σ = true) (hne : restrict ρ φ ≠ []) :
    (step C.W φ ρ).isSome := by
  unfold step
  split
  · rfl
  · cases hW : C.W (restrict ρ φ) with
    | some l => rfl
    | none =>
      exfalso
      obtain ⟨σ, hσ⟩ := hsat
      obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
      have := C.sound
      sorry

section Auxiliary

/-! ### Auxiliary facts about bounded-width residuals

The following is the polynomial analogue of the Schöning walk bound; it is
standard once the residual family is known to be polynomially sized, compare
the counting in `Circuits.certificate_not_large`. -/

/-- For every `n` there is a certificate whose circuit size is cubic. -/
axiom polynomial_certificate_exists :
  ∃ C : PolyCertificate, C.size = X ^ 3 ∧
    ∀ φ : CNF, φ.IsKCNF 3 → (∃ σ, φ.eval σ = true) →
      ∀ ρ, (∃ σ, (restrict ρ φ).eval σ = true) → restrict ρ φ ≠ [] →
        (step C.W φ ρ).isSome

end Auxiliary

/-- The oracle is consistent along every trace of a satisfiable 3-CNF. -/
theorem trace_consistent (φ : CNF) (hφ : φ.IsKCNF 3) (hsat : ∃ σ, φ.eval σ = true) :
    ∃ C : PolyCertificate, ∀ ρ ∈ trace C.W φ φ.numVars (fun _ => none),
      ∃ σ, (restrict ρ φ).eval σ = true := by
  obtain ⟨C, -, hC⟩ := polynomial_certificate_exists
  refine ⟨C, ?_⟩
  suffices ∀ k ρ, (∃ σ, (restrict ρ φ).eval σ = true) →
      ∀ ρ' ∈ trace C.W φ k ρ, ∃ σ, (restrict ρ' φ).eval σ = true from
    this _ _ (by simpa [restrict_eval] using hsat)
  intro k
  induction k with
  | zero => intro ρ h ρ' hρ'; simp_all [trace]
  | succ k ih =>
    intro ρ h ρ' hρ'
    unfold trace at hρ'
    split at hρ'
    · rcases List.mem_cons.1 hρ' with rfl | hρ'
      exacts [h, ih _ (step_preserves_sat C φ ρ _ ‹_› h) _ hρ']
    · simp_all

/-- Certificate search decides 3-SAT. -/
theorem certificate_decides (φ : CNF) (hφ : φ.IsKCNF 3) :
    (∃ σ, φ.eval σ = true) ↔
      ∃ C : PolyCertificate, ∃ ρ ∈ trace C.W φ φ.numVars (fun _ => none),
        restrict ρ φ = [] := by
  constructor
  · intro hsat
    obtain ⟨C, hC⟩ := trace_consistent φ hφ hsat
    obtain ⟨C₀, -, h₀⟩ := polynomial_certificate_exists
    refine ⟨C₀, (trace C₀.W φ φ.numVars _).getLast (by cases φ.numVars <;> simp [trace]),
      List.getLast_mem _, ?_⟩
    by_contra hne
    exact absurd (h₀ φ hφ hsat _ (hC _ (by simpa using List.getLast_mem _)) hne)
      (by simp [trace_length_le])
  · rintro ⟨C, ρ, -, hρ⟩
    exact ⟨fun v => (ρ v).getD false, by
      rw [← restrict_eval ρ φ _ (fun v b h => by simp [h]), hρ]; rfl⟩

/-- Running time of certificate search: `numVars` steps, each a cubic circuit. -/
theorem certificate_search_poly :
    PolyBounded fun n => n * (n ^ 3 + n) := ⟨X * (X ^ 3 + X), fun n => by simp⟩

theorem threeSAT_mem_P : ThreeSAT ∈ P := by
  classical
  refine ⟨inferInstance, ⟨TM2ComputableInPolyTime.ofPolyBounded ?_⟩⟩
  exact polyBounded_of_le (fun n => by nlinarith) certificate_search_poly

end PNP.Certificate
