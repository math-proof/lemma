module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.TwoPointInequality.booleanFourier.twoPointPathFn_c_pos
open Real Set BooleanFourier Bool


public section

/--
[twoPointPathFn_d_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/TwoPointInequality.lean)
-/
@[path]
private theorem main
  {a b t : ℝ}
-- given
  (ha : a ≥ 0)
  (hb : b ≥ 0)
  (hab : 0 < a + b)
  (ht : t ∈ Set.Ioo 0 1) :
-- imply
  0 < (1 - t) / 2 * a + (1 + t) / 2 * b := by
-- proof
  have h1 : (0 : ℝ) < (1 - t) / 2 := by linarith [ht.2]
  have h2 : (0 : ℝ) < (1 + t) / 2 := by linarith [ht.1]
  obtain ha_pos | ha_zero := ha.lt_or_eq
  · linarith [mul_pos h1 ha_pos, mul_nonneg h2.le hb]
  · linarith [mul_nonneg h1.le ha, mul_pos h2 (show (0 : ℝ) < b by linarith [hab, ha_zero.symm])]


theorem BooleanFourier.twoPointPathFn_d_pos
  {a b t : ℝ}
-- given
  (ha : a ≥ 0)
  (hb : b ≥ 0)
  (hab : 0 < a + b)
  (ht : t ∈ Set.Ioo 0 1) :
-- imply
  0 < (1 - t) / 2 * a + (1 + t) / 2 * b :=
-- proof
  main ha hb hab ht


-- created on 2026-10-23
-- updated on 2026-11-24
