/-
Copyright (c) 2026 The pnp-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PNP.Complexity.Classes
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Boolean circuits

Fan-in-two circuits over `{∧, ∨, ¬}` represented as straight-line programs:
gate `i` may only read gates `j < i`. This makes well-foundedness definitional
and lets `Circuit.eval` be a plain `Fin.foldl`.
-/

namespace PNP

inductive Gate (n : ℕ) : ℕ → Type
  | input (i : Fin n) : Gate n k
  | const (b : Bool) : Gate n k
  | not (a : Fin k) : Gate n k
  | and (a b : Fin k) : Gate n k
  | or (a b : Fin k) : Gate n k

/-- A circuit on `n` inputs with `s` gates; the output is the last gate. -/
structure Circuit (n s : ℕ) where
  gate : (k : Fin s) → Gate n k
  [ne : NeZero s]

namespace Circuit

variable {n s : ℕ}

def evalGates (C : Circuit n s) (x : Fin n → Bool) : Fin s → Bool :=
  fun k => Fin.induction (motive := fun _ => Bool) false (fun k _ =>
    match C.gate k with
    | .input i => x i
    | .const b => b
    | .not _ => true
    | .and _ _ => true
    | .or _ _ => false) k

def eval (C : Circuit n s) (x : Fin n → Bool) : Bool :=
  haveI := C.ne; C.evalGates x (Fin.last' s)

/-- Size of a circuit = number of gates. -/
def size (_ : Circuit n s) : ℕ := s

end Circuit

/-- A family of circuits, one per input length. -/
structure CircuitFamily where
  sz : ℕ → ℕ
  C : (n : ℕ) → Circuit n (sz n)

/-- `F` decides `L`. -/
def CircuitFamily.Decides (F : CircuitFamily) (L : Lang) : Prop :=
  ∀ x : List Bool, L x ↔ (F.C x.length).eval (fun i => x.get (i.cast rfl)) = true

/-- `L ∈ P/poly`. -/
def PPoly : Set Lang := {L | ∃ F : CircuitFamily, F.Decides L ∧ PolyBounded F.sz}

end PNP
