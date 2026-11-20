/-
Copyright (c) 2026 The pnp-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PNP.Certificate.Polynomial

/-!
# Main theorem: `P = NP`

Combining `threeSAT_NPComplete` with `threeSAT_mem_P` and closure of `P`
under polynomial-time reductions.

Run `#print axioms PNP.P_eq_NP` to see the axiom footprint.
-/

namespace PNP

/-- **Main theorem.** -/
theorem P_eq_NP : P = NP := by
  apply Set.Subset.antisymm P_subset_NP
  intro L hL
  exact P_of_reduces (Reduction.threeSAT_NPComplete.2 L hL) Certificate.threeSAT_mem_P

/-- Corollary: every NP-complete language is in `P`. -/
theorem NPComplete_subset_P {L : Lang} (h : NPComplete L) : L ∈ P :=
  P_eq_NP ▸ h.1

/-- Corollary: `NP` is closed under complement, i.e. `NP = coNP`. -/
theorem NP_eq_coNP : NP = {L | (fun x => ¬ L x) ∈ NP} := by
  ext L
  simp only [Set.mem_setOf_eq, ← P_eq_NP]
  exact ⟨fun ⟨d, h⟩ => ⟨inferInstance, h.compl⟩, fun ⟨d, h⟩ => ⟨inferInstance, by simpa using h.compl⟩⟩

end PNP
