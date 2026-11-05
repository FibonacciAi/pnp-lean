/-
Copyright (c) 2026 The pnp-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PNP.Complexity.Classes
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Sort

/-!
# Propositional CNF formulas

Literals, clauses and CNF formulas over variables indexed by `ℕ`, with
evaluation, a canonical bit encoding, and the language `SAT`.

We keep clauses as `List Literal` rather than `Finset Literal`: duplicate
literals are harmless for satisfiability and lists make the encoding (and
therefore the polynomial bounds) completely explicit.
-/

namespace PNP

/-- A literal: a variable index and a polarity. -/
structure Literal where
  var : ℕ
  pos : Bool
  deriving DecidableEq, Repr, Inhabited

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Literal

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF := List Clause

/-- A truth assignment. -/
abbrev Assignment := ℕ → Bool

namespace Literal

def eval (σ : Assignment) (l : Literal) : Bool := if l.pos then σ l.var else !σ l.var

@[simp] theorem eval_neg (σ : Assignment) (l : Literal) :
    eval σ ⟨l.var, !l.pos⟩ = !eval σ l := by
  cases l with | mk v p => cases p <;> simp [eval]

end Literal

def Clause.eval (σ : Assignment) (c : Clause) : Bool := c.any (Literal.eval σ)
def CNF.eval (σ : Assignment) (φ : CNF) : Bool := φ.all (Clause.eval σ)

/-- Largest variable index occurring in `φ` (plus one). -/
def CNF.numVars (φ : CNF) : ℕ := (φ.flatMap (List.map Literal.var)).foldr (max · ∘ (· + 1)) 0

/-- `φ` is a k-CNF if every clause has at most `k` literals. -/
def CNF.IsKCNF (k : ℕ) (φ : CNF) : Prop := ∀ c ∈ φ, c.length ≤ k

/-- Self-delimiting unary-length / binary-index bit encoding. -/
def encodeLit (l : Literal) : List Bool :=
  List.replicate (Nat.size l.var) true ++ false :: Nat.bits l.var ++ [l.pos]

def encodeCNF (φ : CNF) : List Bool :=
  φ.flatMap fun c => (c.flatMap encodeLit) ++ [false, false]

/-- Left inverse of `encodeCNF` (returns `[]` on malformed input). -/
def decodeCNF : List Bool → CNF
  | [] => []
  | bs =>
    let (c, rest) := decodeClause bs
    c :: decodeCNF rest
decreasing_by exact decodeClause_lt bs ‹_›

@[simp] theorem decodeCNF_encodeCNF (φ : CNF) : decodeCNF (encodeCNF φ) = φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih => rw [encodeCNF, List.flatMap_cons, decodeCNF, decodeClause_append]; simp [ih]

theorem encodeCNF_length_le (φ : CNF) :
    (encodeCNF φ).length ≤ 4 * (φ.length + φ.join.length) * (Nat.size φ.numVars + 1) := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c φ ih =>
    simp only [encodeCNF, List.flatMap_cons, List.length_append] at *
    nlinarith [Nat.size_le_size (Nat.le_succ φ.numVars)]

/-- The language of satisfiable (encoded) CNF formulas. -/
def SAT : Lang := fun x => ∃ φ : CNF, encodeCNF φ = x ∧ ∃ σ, φ.eval σ = true

/-- The language of satisfiable 3-CNF formulas. -/
def ThreeSAT : Lang := fun x => ∃ φ : CNF, encodeCNF φ = x ∧ φ.IsKCNF 3 ∧ ∃ σ, φ.eval σ = true

end PNP
