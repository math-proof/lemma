import Mathlib
import sympy.Basic



@[main]
private lemma main
  [DecidableEq α]
  {n : ℕ}
  {A : Fin n → Finset α} :
-- imply
  (Finset.univ.biUnion A).card =
    ∑ k : Fin n, (-1 : ℤ) ^ (k.val + 1) *
      ((Finset.powersetCard (k.val + 1) Finset.univ).sum fun S ↦
        ((Finset.univ.filter fun i ↦ i ∈ S.val).biUnion A).card : ℤ) := by
-- proof
  sorry


-- created on 2026-10-07
