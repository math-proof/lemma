import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalMomentum
open StatMech StatMech.FrontierA


/--
[one_sub_cos_add_le_two_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalMomentum.lean)
-/
@[path]
private lemma one_sub_cos_add_le_two_sum_eq
  {p q : ℝ} :
-- imply
  1 - Real.cos (p + q) ≤ 2 * ((1 - Real.cos p) + (1 - Real.cos q)) := by
-- proof
  apply StatMech.FrontierA.one_sub_cos_add_le_two_sum p q

/--
[triangularIsingSymbol_sub_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalMomentum.lean)
-/
@[path]
private lemma triangularIsingSymbol_sub_zero_eq
  {x y p q : ℝ} :
-- imply
  triangularIsingSymbol x x y p q - triangularIsingSymbol x x y 0 0 = Real.sinh (2 * x) * ((1 - Real.cos p) + (1 - Real.cos q)) + Real.sinh (2 * y) * (1 - Real.cos (p + q)) := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_sub_zero x y p q

/--
[exists_triangularIsingSymbol_quadratic_lower_at_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalMomentum.lean)
-/
@[path]
private lemma exists_triangularIsingSymbol_quadratic_lower_at_root_eq
  {β J : ℝ}
-- given
  (hβ : 0 < β)
  (hroot : triangularIsingCriticalRate β (β * J) = 1) :
-- imply
  ∃ c : ℝ, 0 < c ∧ ∀ p q : ℝ, := by
-- proof
  apply StatMech.FrontierA.exists_triangularIsingSymbol_quadratic_lower_at_root hβ hroot


-- created on 2026-10-23
