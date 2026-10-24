import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexNormalizedCountingMidpoint
open Set StatMech StatMech.FrontierD


/--
[abs_log_sub_log_sub_div_le_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNormalizedCountingMidpoint.lean)
-/
@[path]
private lemma abs_log_sub_log_sub_div_le_of_lower_eq :
-- imply
  ∀ {lower x y : Real} (hlower : 0 < lower) (hx : lower <= x) (hy : lower <= y), |Real.log x - Real.log y - (x - y) / y| <= |x - y| ^ 2 / lower ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_log_sub_log_sub_div_le_of_lower

/--
[abs_two_log_sub_log_sub_log_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNormalizedCountingMidpoint.lean)
-/
@[path]
private lemma abs_two_log_sub_log_sub_log_le_eq :
-- imply
  ∀ {lower x y z E D : Real} (hlower : 0 < lower) (hx : lower <= x) (hy : lower <= y) (hz : lower <= z) (hmid : |2 * y - x - z| <= E) (hxy : |x - y| <= D) (hzy : |z - y| <= D), |2 * Real.log y - Real.log x - Real.log z| <= E / lower + 2 * D ^ 2 / lower ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_two_log_sub_log_sub_log_le

/--
[abs_normalized_midpoint_defect_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNormalizedCountingMidpoint.lean)
-/
@[path]
private lemma abs_normalized_midpoint_defect_le_eq :
-- imply
  ∀ {a b Fa Fb Fm L : Real} (ha : 0 < a) (hab : a <= b) (hL : 0 <= L) (hmid : |Fm - (Fa + Fb) / 2| <= L * (b - a) ^ 2 / 4) (hmass : |(Fb - Fa) - (b - a) * (Fa / a)| <= L * (b - a) * b), |2 * (Fm / ((a + b) / 2)) - Fa / a - Fb / b| <= L * (b - a) ^ 2 / a := by
-- proof
  apply StatMech.FrontierD.abs_normalized_midpoint_defect_le

/--
[abs_normalized_log_midpoint_defect_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNormalizedCountingMidpoint.lean)
-/
@[path]
private lemma abs_normalized_log_midpoint_defect_le_eq :
-- imply
  ∀ {lower R a b Fa Fb Fm L : Real} (hlower : 0 < lower) (hR : 0 <= R) (ha : 0 < a) (hab : a <= b) (hL : 0 <= L) (hratio : b - a <= R * a) (hAa : lower <= Fa / a) (hAm : lower <= Fm / ((a + b) / 2)) (hAb : lower <= Fb / b) (hmid : |Fm - (Fa + Fb) / 2| <= L * (b - a) ^ 2 / 4) (hmass : |(Fb - Fa) - (b - a) * (Fa / a)| <= L * (b - a) * b), |2 * Real.log (Fm / ((a + b) / 2)) - Real.log (Fa / a) - Real.log (Fb / b)| <= (L * (b - a) ^ 2 / a) / lower + 2 * (L * (b - a) * (3 + R)) ^ 2 / lower ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_normalized_log_midpoint_defect_le


-- created on 2026-10-23
