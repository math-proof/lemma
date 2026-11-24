module
public import Mathlib
public import Notation.Algebra.Power
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.TwoPointInequality.booleanFourier.twoPointPathFn_d_pos
open Real Set BooleanFourier Bool


public section

/--
[twoPointPathFn_base_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/TwoPointInequality.lean)
-/
@[path]
private theorem main
  {p a b t : ℝ}
-- given
  (ha : a ≥ 0)
  (hb : b ≥ 0)
  (hab : 0 < a + b)
  (ht : t ∈ Set.Ioo 0 1) :
-- imply
  0 < (((1 + t) / 2 * a + (1 - t) / 2 * b) ^ (1 + (p - 1) / t²) + ((1 - t) / 2 * a + (1 + t) / 2 * b) ^ (1 + (p - 1) / t²)) / 2 :=
-- proof
  div_pos (add_pos_of_pos_of_nonneg
    (rpow_pos_of_pos (twoPointPathFn_c_pos ha hb hab ht) _)
    (rpow_nonneg (twoPointPathFn_d_pos ha hb hab ht).le _)) two_pos


theorem BooleanFourier.twoPointPathFn_base_pos
  {p a b t : ℝ}
-- given
  (ha : a ≥ 0)
  (hb : b ≥ 0)
  (hab : 0 < a + b)
  (ht : t ∈ Set.Ioo 0 1) :
-- imply
  0 < (((1 + t) / 2 * a + (1 - t) / 2 * b) ^ (1 + (p - 1) / t²) + ((1 - t) / 2 * a + (1 + t) / 2 * b) ^ (1 + (p - 1) / t²)) / 2 :=
-- proof
  main ha hb hab ht


-- created on 2026-10-23
-- updated on 2026-11-24
