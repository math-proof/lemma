import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.TwoPointInequality
open Real Set BooleanFourier


namespace BooleanFourier

/--
[twoPointPathFn_c_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/TwoPointInequality.lean)
-/
@[path]
lemma twoPointPathFn_c_pos
  {a b : ℝ}
  {t : ℝ}
-- given
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hab : 0 < a + b)
  (ht : t ∈ Set.Ioo 0 1) :
-- imply
  0 < (1 + t) / 2 * a + (1 - t) / 2 * b := by
-- proof
  have h1 : (0 : ℝ) < (1 + t) / 2 := by linarith [ht.1]
  have h2 : (0 : ℝ) < (1 - t) / 2 := by linarith [ht.2]
  obtain ha_pos | ha_zero := ha.lt_or_eq
  · linarith [mul_pos h1 ha_pos, mul_nonneg h2.le hb]
  · linarith [mul_nonneg h1.le ha, mul_pos h2 (show (0 : ℝ) < b by linarith [ha_zero.symm])]

end BooleanFourier

namespace BooleanFourier

/--
[twoPointPathFn_d_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/TwoPointInequality.lean)
-/
@[path]
lemma twoPointPathFn_d_pos
  {a b : ℝ}
  {t : ℝ}
-- given
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hab : 0 < a + b)
  (ht : t ∈ Set.Ioo 0 1) :
-- imply
  0 < (1 - t) / 2 * a + (1 + t) / 2 * b := by
-- proof
  have h1 : (0 : ℝ) < (1 - t) / 2 := by linarith [ht.2]
  have h2 : (0 : ℝ) < (1 + t) / 2 := by linarith [ht.1]
  obtain ha_pos | ha_zero := ha.lt_or_eq
  · linarith [mul_pos h1 ha_pos, mul_nonneg h2.le hb]
  · linarith [mul_nonneg h1.le ha, mul_pos h2 (show (0 : ℝ) < b by linarith [ha_zero.symm])]

end BooleanFourier

namespace BooleanFourier

/--
[twoPointPathFn_base_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/TwoPointInequality.lean)
-/
@[path]
lemma twoPointPathFn_base_pos
  {p a b : ℝ}
  {t : ℝ}
-- given
  (_hp : 1 < p)
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hab : 0 < a + b)
  (ht : t ∈ Set.Ioo 0 1) :
-- imply
  0 < (((1 + t) / 2 * a + (1 - t) / 2 * b) ^ (1 + (p - 1) / t ^ 2) + ((1 - t) / 2 * a + (1 + t) / 2 * b) ^ (1 + (p - 1) / t ^ 2)) / 2 :=
-- proof
  div_pos (add_pos_of_pos_of_nonneg
    (rpow_pos_of_pos (twoPointPathFn_c_pos ha hb hab ht) _)
    (rpow_nonneg (twoPointPathFn_d_pos ha hb hab ht).le _)) two_pos

end BooleanFourier


-- created on 2026-10-23
