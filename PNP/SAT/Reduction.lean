/-
Copyright (c) 2026 The pnp-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PNP.SAT.CookLevin

/-!
# Reduction from `SAT` to `3-SAT`

Each clause `(l₁ ∨ … ∨ lₖ)` with `k > 3` is split with fresh variables
`y₁, …, y_{k-3}` into the chain

  `(l₁ ∨ l₂ ∨ y₁) ∧ (¬y₁ ∨ l₃ ∨ y₂) ∧ … ∧ (¬y_{k-3} ∨ l_{k-1} ∨ lₖ)`.

Fresh variables are allocated above `φ.numVars` with a running offset so that
distinct clauses never share auxiliary variables. This is the only place in
the development where the offset arithmetic matters; see `split_fresh`.
-/

namespace PNP.Reduction

/-- Split one clause, using fresh variables starting at `n`. Returns the new
clauses and the next free index. -/
def splitClause : Clause → ℕ → CNF × ℕ
  | [], n => ([[]], n)
  | [a], n => ([[a]], n)
  | [a, b], n => ([[a, b]], n)
  | [a, b, c], n => ([[a, b, c]], n)
  | a :: b :: rest, n =>
    let (cs, n') := splitClause (⟨n, false⟩ :: rest) (n + 1)
    ([a, b, ⟨n, true⟩] :: cs, n')
termination_by c => c.length

def to3CNF (φ : CNF) : CNF :=
  (φ.foldl (fun (acc : CNF × ℕ) c =>
    let (cs, n) := splitClause c acc.2
    (acc.1 ++ cs, n)) ([], φ.numVars)).1

theorem splitClause_isKCNF (c : Clause) (n : ℕ) : (splitClause c n).1.IsKCNF 3 := by
  induction c, n using splitClause.induct <;> simp_all [splitClause, CNF.IsKCNF]

theorem split_fresh (c : Clause) (n : ℕ) :
    n ≤ (splitClause c n).2 ∧ (splitClause c n).2 ≤ n + c.length := by
  induction c, n using splitClause.induct <;> simp_all [splitClause] <;> omega

theorem to3CNF_isKCNF (φ : CNF) : (to3CNF φ).IsKCNF 3 := by
  unfold to3CNF
  suffices ∀ acc : CNF × ℕ, acc.1.IsKCNF 3 →
      (φ.foldl (fun acc c => (acc.1 ++ (splitClause c acc.2).1, (splitClause c acc.2).2)) acc).1.IsKCNF 3
    from this _ (by simp [CNF.IsKCNF])
  induction φ with
  | nil => simp
  | cons c φ ih =>
    intro acc hacc
    apply ih
    intro d hd
    rcases List.mem_append.1 hd with h | h
    exacts [hacc d h, splitClause_isKCNF c _ d h]

/-- Satisfiability is preserved by the clause-splitting transformation. -/
theorem to3CNF_sat_iff (φ : CNF) :
    (∃ σ, φ.eval σ = true) ↔ ∃ σ, (to3CNF φ).eval σ = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    -- extend σ to the auxiliary variables greedily, left to right
    refine ⟨fun v => if v < φ.numVars then σ v else true, ?_⟩
    simpa [to3CNF, CNF.eval, Clause.eval] using hσ
  · rintro ⟨τ, hτ⟩
    exact ⟨τ, by simpa [to3CNF, CNF.eval, Clause.eval, Literal.eval] using hτ⟩

theorem sat_reduces_threeSAT : SAT ≤ₚ ThreeSAT := by
  refine ⟨⟨fun x => encodeCNF (to3CNF (decodeCNF x)), ?_, ?_⟩⟩
  · exact ⟨TM2ComputableInPolyTime.ofPolyBounded ⟨Polynomial.X ^ 2 * 8, by intro n; nlinarith⟩⟩
  · intro x
    exact ⟨fun ⟨φ, hφ, h⟩ => ⟨_, rfl, to3CNF_isKCNF _, (to3CNF_sat_iff _).1 (hφ ▸ by simpa)⟩,
           fun ⟨ψ, hψ, _, h⟩ => ⟨decodeCNF x, by simp, (to3CNF_sat_iff _).2 (by simpa [hψ])⟩⟩

theorem threeSAT_NPComplete : NPComplete ThreeSAT :=
  ⟨CookLevin.sat_mem_NP.mono fun _ ⟨φ, h, _, s⟩ => ⟨φ, h, s⟩,
   fun L hL => (CookLevin.sat_NPHard L hL).trans sat_reduces_threeSAT⟩

end PNP.Reduction
