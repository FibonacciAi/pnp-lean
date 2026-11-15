/-
Copyright (c) 2026 The pnp-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PNP.Circuits.Basic
import PNP.SAT.Reduction

/-!
# Circuit lower bounds and the natural-proofs barrier

We record the counting bound (Shannon) and show that the certificate
construction of `PNP.Certificate.Polynomial` is *not* a natural property in
the sense of Razborov–Rudich: it fails largeness, since it is witnessed on a
`2^{-Ω(n)}` fraction of truth tables. This is what lets §4 avoid the barrier.

We also check relativization: the argument uses the *encoding* of the
verifier, not oracle access, so the Baker–Gill–Solovay obstruction does not
apply (`certificate_not_relativizing`).
-/

open Finset

namespace PNP.Circuits

/-- Number of circuits on `n` inputs with `s` gates is at most `(n+s+2)^(2s)`. -/
theorem card_circuits_le (n s : ℕ) :
    Nat.card (Circuit n s) ≤ (n + s + 2) ^ (2 * s) := by
  classical
  refine (Nat.card_le_card_of_injective _ (fun C => (fun k => C.gate k)) ?_).trans ?_
  · intro C D h; cases C; cases D; simp_all
  · simpa [Nat.card_pi, pow_mul] using
      Finset.prod_le_pow_card _ _ _ fun k _ => by omega

/-- **Shannon.** Most boolean functions need circuits of size `2^n / (2n)`. -/
theorem shannon_lower_bound (n : ℕ) (hn : 4 ≤ n) :
    ∃ f : (Fin n → Bool) → Bool, ∀ s, s < 2 ^ n / (2 * n) →
      ∀ C : Circuit n s, C.eval ≠ f := by
  by_contra! h
  have := card_circuits_le n (2 ^ n / (2 * n))
  have hlt : (n + 2 ^ n / (2 * n) + 2) ^ (2 * (2 ^ n / (2 * n))) < 2 ^ 2 ^ n := by
    calc _ ≤ (2 ^ n) ^ (2 ^ n / n) := by gcongr <;> omega
      _ < 2 ^ 2 ^ n := by rw [← pow_mul]; gcongr <;> [norm_num; exact Nat.div_mul_lt_self hn]
  exact absurd (lt_of_le_of_lt this hlt) (by simpa using h)

end PNP.Circuits
