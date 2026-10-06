import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : Fin n → ℂ} :
-- imply
  Set.univ \ (↑(Finset.univ.image x) : Set ℂ) ≠ ∅ := by
-- proof
  apply Set.nonempty_iff_ne_empty.mp
  apply Set.Infinite.nonempty
  apply Set.Infinite.sdiff Set.infinite_univ
  exact Set.finite_coe_iff.mpr (Finset.finite_toSet _)


-- created on 2021-04-24
