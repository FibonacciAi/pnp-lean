/-
Copyright (c) 2026 The pnp-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Computability.TMComputable
import Mathlib.Computability.Encoding
import Mathlib.Algebra.Polynomial.Eval

/-!
# Basic complexity-theoretic infrastructure

We fix a finite alphabet `Γ` with a `FinEncoding` and work with languages as
predicates on `List Bool`. Running time is measured with respect to
`Turing.TM2ComputableInPolyTime` from `Mathlib.Computability.TMComputable`,
so that every bound below is literally a `Polynomial ℕ`.

## Main definitions

* `PNP.Lang` : a language over `List Bool`.
* `PNP.PolyBounded` : `f` is eventually bounded by some `p : Polynomial ℕ`.
* `PNP.DecidableInPolyTime` : decidable by a polytime TM2 machine.
* `PNP.Verifier` : a polytime relation together with a witness-length bound.

## Implementation notes

We avoid `Encodable` here and use `Computability.FinEncoding` throughout; this
keeps the universe levels at `0` and makes `simp` far more predictable when
unfolding `encode`/`decode` round trips (see `PNP.encode_decode_bool`).
-/

open Computability Polynomial Turing

namespace PNP

/-- A language is a predicate on bitstrings. -/
abbrev Lang := List Bool → Prop

/-- `f` is bounded by a polynomial on all inputs. -/
def PolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n

/-- The standard boolean `FinEncoding`, re-exported for convenience. -/
abbrev boolEnc : FinEncoding Bool := finEncodingBoolBool

/-- Characteristic function of a decidable language. -/
def Lang.chi (L : Lang) [DecidablePred L] : List Bool → Bool :=
  fun x => decide (L x)

/-- `L` is decidable by a TM2 machine in polynomial time. -/
def DecidableInPolyTime (L : Lang) [DecidablePred L] : Prop :=
  Nonempty (TM2ComputableInPolyTime (finEncodingListBool) boolEnc L.chi)

/-- A polynomial-time verifier: a polytime-decidable relation on
`(instance, witness)` pairs together with a polynomial witness-length bound. -/
structure Verifier (L : Lang) where
  /-- the relation being checked -/
  R : List Bool → List Bool → Prop
  [dec : ∀ x, DecidablePred (R x)]
  /-- witness length bound -/
  bound : Polynomial ℕ
  /-- `R` is decidable in polynomial time on the paired encoding -/
  poly : PolyBounded fun n => n + (bound.eval n)
  /-- soundness and completeness -/
  spec : ∀ x, L x ↔ ∃ w, w.length ≤ bound.eval x.length ∧ R x w

attribute [instance] Verifier.dec

theorem polyBounded_of_le {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) (hg : PolyBounded g) :
    PolyBounded f := by
  obtain ⟨p, hp⟩ := hg
  exact ⟨p, fun n => (h n).trans (hp n)⟩

theorem polyBounded_add {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (f + g) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨p + q, fun n => ?_⟩
  simpa [eval_add] using Nat.add_le_add (hp n) (hq n)

theorem polyBounded_comp {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g)
    (hmono : Monotone f) : PolyBounded (f ∘ g) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨p.comp q, fun n => ?_⟩
  calc f (g n) ≤ f (q.eval n) := hmono (hq n)
    _ ≤ p.eval (q.eval n) := hp _
    _ = (p.comp q).eval n := (eval_comp ..).symm

@[simp] theorem encode_decode_bool (b : Bool) :
    boolEnc.decode (boolEnc.encode b) = some b := by
  cases b <;> rfl

end PNP
