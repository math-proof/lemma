import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHardCrossingOrientationNoGo.Part2
open StatMech StatMech.FrontierD


/--
[FKRectWideCrossingScalarData.easy_ge_one_div_eight_mul_pow_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHardCrossingOrientationNoGo.lean)
-/
@[path]
private lemma easy_ge_one_div_eight_mul_pow_six_eq
  {q hard easy : Real}
  {data : FKRectWideCrossingScalarData q hard easy}
-- given
  (hq : 1 <= q) :
-- imply
  1 / (8 * q ^ 6) <= easy := by
-- proof
  apply StatMech.FrontierD.FKRectWideCrossingScalarData.easy_ge_one_div_eight_mul_pow_six hq data

/--
[fkRectWideCrossingScalarData_zero_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHardCrossingOrientationNoGo.lean)
-/
@[path]
private lemma fkRectWideCrossingScalarData_zero_one_eq
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  FKRectWideCrossingScalarData q 0 1 := by
-- proof
  apply StatMech.FrontierD.fkRectWideCrossingScalarData_zero_one hq

/--
[not_exists_positive_hardFloor_of_wideCrossingScalarData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHardCrossingOrientationNoGo.lean)
-/
@[path]
private lemma not_exists_positive_hardFloor_of_wideCrossingScalarData_eq
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  ¬ (exists floor : Real, 0 < floor /\ forall hard easy : Real, FKRectWideCrossingScalarData q hard easy -> floor <= hard) := by
-- proof
  apply StatMech.FrontierD.not_exists_positive_hardFloor_of_wideCrossingScalarData hq

/--
[exists_wideCrossingScalarData_not_reverseOrientationBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHardCrossingOrientationNoGo.lean)
-/
@[path]
private lemma exists_wideCrossingScalarData_not_reverseOrientationBridge_eq
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  exists hard easy : Real, FKRectWideCrossingScalarData q hard easy /\ ¬ FKRectWideCrossingReverseOrientationBridge q hard easy := by
-- proof
  apply StatMech.FrontierD.exists_wideCrossingScalarData_not_reverseOrientationBridge hq

/--
[FKRectWideCrossingScalarData.hard_ge_of_reverseOrientationBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHardCrossingOrientationNoGo.lean)
-/
@[path]
private lemma hard_ge_of_reverseOrientationBridge_eq
  {q hard easy : Real}
  {data : FKRectWideCrossingScalarData q hard easy}
-- given
  (hq : 1 <= q)
  (hreverse : FKRectWideCrossingReverseOrientationBridge q hard easy) :
-- imply
  1 / (8 * q ^ 2) <= hard := by
-- proof
  apply StatMech.FrontierD.FKRectWideCrossingScalarData.hard_ge_of_reverseOrientationBridge hq data hreverse


-- created on 2026-10-23
