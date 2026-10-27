import Mathlib.Algebra.Order.Floor.Ring
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
  {a : ℤ}
-- given
  (h : x ∈ Set.Ico (a : ℝ) (a + 1)) :
-- imply
  ⌊x⌋ = a := by
-- proof
  exact Int.floor_eq_iff.mpr ⟨h.1, h.2⟩


-- created on 2019-12-05
