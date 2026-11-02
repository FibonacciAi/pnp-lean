/-
Copyright (c) 2026 The pnp-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PNP.Complexity.Basic

/-!
# The classes `P` and `NP`

`P` is the class of languages decidable in polynomial time; `NP` is the class
of languages admitting a polynomial-time `Verifier`. We also define
polynomial-time many-one reductions `L₁ ≤ₚ L₂` and prove the expected
closure lemmas.
-/

open Computability Turing

namespace PNP

/-- The complexity class `P`. -/
def P : Set Lang := {L | ∃ _ : DecidablePred L, DecidableInPolyTime L}

/-- The complexity class `NP`. -/
def NP : Set Lang := {L | Nonempty (Verifier L)}

/-- Polynomial-time many-one reduction. -/
structure PolyReduction (L₁ L₂ : Lang) where
  f : List Bool → List Bool
  comp : Nonempty (TM2ComputableInPolyTime finEncodingListBool finEncodingListBool f)
  correct : ∀ x, L₁ x ↔ L₂ (f x)

@[inherit_doc] infix:50 " ≤ₚ " => fun L₁ L₂ => Nonempty (PolyReduction L₁ L₂)

/-- `L` is NP-hard if every NP language reduces to it. -/
def NPHard (L : Lang) : Prop := ∀ L' ∈ NP, L' ≤ₚ L

/-- `L` is NP-complete. -/
def NPComplete (L : Lang) : Prop := L ∈ NP ∧ NPHard L

theorem PolyReduction.refl (L : Lang) : L ≤ₚ L :=
  ⟨⟨id, ⟨TM2ComputableInPolyTime.id finEncodingListBool⟩, fun _ => Iff.rfl⟩⟩

theorem PolyReduction.trans {L₁ L₂ L₃ : Lang} :
    L₁ ≤ₚ L₂ → L₂ ≤ₚ L₃ → L₁ ≤ₚ L₃ := by
  rintro ⟨⟨f, ⟨hf⟩, hf'⟩⟩ ⟨⟨g, ⟨hg⟩, hg'⟩⟩
  exact ⟨⟨g ∘ f, ⟨hf.comp hg⟩, fun x => (hf' x).trans (hg' (f x))⟩⟩

/-- Every language in `P` has a trivial verifier (empty witness). -/
theorem P_subset_NP : P ⊆ NP := by
  rintro L ⟨hdec, hpoly⟩
  refine ⟨{ R := fun x _ => L x, bound := 0, poly := ⟨Polynomial.X, by simp⟩,
            spec := fun x => ⟨fun h => ⟨[], by simp, h⟩, fun ⟨_, _, h⟩ => h⟩ }⟩

end PNP
