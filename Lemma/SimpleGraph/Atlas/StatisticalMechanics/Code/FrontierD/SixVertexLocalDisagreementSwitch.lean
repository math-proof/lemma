import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch
open Finset Matrix StatMech StatMech.FrontierD


/--
[exists_sixVertexLocalSwapTwo_of_disagreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma exists_sixVertexLocalSwapTwo_of_disagreement_eq
  {p q : SixVertexLocalIncomingPattern}
  {d : Fin 4}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hd : p d ≠ q d)
  (hnotCC : Not (p.IsCType /\ q.IsCType)) :
-- imply
  exists e : Fin 4, e ≠ d /\ p e ≠ q e /\ (sixVertexLocalSwapTwo p q d e).1.Ice /\ (sixVertexLocalSwapTwo p q d e).2.Ice /\ sixVertexLocalCTypeCount p q <= sixVertexLocalCTypeCount (sixVertexLocalSwapTwo p q d e).1 (sixVertexLocalSwapTwo p q d e).2 := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexLocalSwapTwo_of_disagreement p q d hp hq hd hnotCC

/--
[sixVertexLocal_all_disagree_of_ice_cType](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexLocal_all_disagree_of_ice_cType_eq
  {p q : SixVertexLocalIncomingPattern}
  {d : Fin 4}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hpc : p.IsCType)
  (hqc : q.IsCType)
  (hd : p d ≠ q d) :
-- imply
  forall i : Fin 4, p i ≠ q i := by
-- proof
  apply StatMech.FrontierD.sixVertexLocal_all_disagree_of_ice_cType p q d hp hq hpc hqc hd

/--
[sixVertexLocalPatternWeight_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexLocalPatternWeight_eq_pow_eq
  {c : Real}
  {p : SixVertexLocalIncomingPattern}
-- given
  (hp : p.Ice) :
-- imply
  sixVertexLocalPatternWeight c p = c ^ (if p.IsCType then 1 else 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalPatternWeight_eq_pow c p hp

/--
[exists_sixVertexLocalSwapTwo_weight_product_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma exists_sixVertexLocalSwapTwo_weight_product_le_eq
  {c : Real}
  {p q : SixVertexLocalIncomingPattern}
  {d : Fin 4}
-- given
  (hc : 1 <= c)
  (hp : p.Ice)
  (hq : q.Ice)
  (hd : p d ≠ q d)
  (hnotCC : Not (p.IsCType /\ q.IsCType)) :
-- imply
  exists e : Fin 4, e ≠ d /\ p e ≠ q e /\ (sixVertexLocalSwapTwo p q d e).1.Ice /\ (sixVertexLocalSwapTwo p q d e).2.Ice /\ sixVertexLocalPatternWeight c p * sixVertexLocalPatternWeight c q <= sixVertexLocalPatternWeight c (sixVertexLocalSwapTwo p q d e).1 * sixVertexLocalPatternWeight c (sixVertexLocalSwapTwo p q d e).2 := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexLocalSwapTwo_weight_product_le hc p q d hp hq hd hnotCC

/--
[sixVertexLocalIncomingPattern_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexLocalIncomingPattern_count_eq
  {omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  sixVertexLocalIncomingCount (sixVertexLocalIncomingPattern omega v) = omega.incomingCount v := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalIncomingPattern_count omega v

/--
[sixVertexLocalIncomingPattern_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexLocalIncomingPattern_ice_eq
  {omega : SixVertexArrows T}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule) :
-- imply
  (sixVertexLocalIncomingPattern omega v).Ice := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalIncomingPattern_ice omega homega v

/--
[sixVertexLocalIncomingPattern_isCType_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexLocalIncomingPattern_isCType_iff_eq
  {omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  (sixVertexLocalIncomingPattern omega v).IsCType <-> omega.IsCType v := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalIncomingPattern_isCType_iff omega v

/--
[sixVertexLocalPatternWeight_eq_localWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexLocalPatternWeight_eq_localWeight_eq
  {c : Real}
  {omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  sixVertexLocalPatternWeight c (sixVertexLocalIncomingPattern omega v) = omega.localWeight c v := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalPatternWeight_eq_localWeight c omega v

/--
[sixVertexRectangleLocalIncomingPattern_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexRectangleLocalIncomingPattern_count_eq
  {omega : SixVertexRectangleArrows N M}
  {v : Fin N × Fin M} :
-- imply
  sixVertexLocalIncomingCount (sixVertexRectangleLocalIncomingPattern omega v) = omega.incomingCount v := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleLocalIncomingPattern_count omega v

/--
[sixVertexRectangleLocalIncomingPattern_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexRectangleLocalIncomingPattern_ice_eq
  {omega : SixVertexRectangleArrows N M}
  {v : Fin N × Fin M}
-- given
  (homega : omega.IceRule) :
-- imply
  (sixVertexRectangleLocalIncomingPattern omega v).Ice := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleLocalIncomingPattern_ice omega homega v

/--
[sixVertexRectangleLocalIncomingPattern_isCType_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexRectangleLocalIncomingPattern_isCType_iff_eq
  {omega : SixVertexRectangleArrows N M}
  {v : Fin N × Fin M} :
-- imply
  (sixVertexRectangleLocalIncomingPattern omega v).IsCType <-> omega.IsCType v := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleLocalIncomingPattern_isCType_iff omega v

/--
[sixVertexRectangleLocalPatternWeight_eq_localWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexRectangleLocalPatternWeight_eq_localWeight_eq
  {c : Real}
  {omega : SixVertexRectangleArrows N M}
  {v : Fin N × Fin M} :
-- imply
  sixVertexLocalPatternWeight c (sixVertexRectangleLocalIncomingPattern omega v) = omega.localWeight c v := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleLocalPatternWeight_eq_localWeight c omega v

/--
[exists_sixVertexLocalSwapMask_of_disagreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma exists_sixVertexLocalSwapMask_of_disagreement_eq
  {p q : SixVertexLocalIncomingPattern}
  {d : Fin 4}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hd : p d ≠ q d) :
-- imply
  exists mask : SixVertexLocalIncomingPattern, mask d = true /\ (forall i, mask i = true -> p i ≠ q i) /\ (sixVertexLocalSwapMask p q mask).1.Ice /\ (sixVertexLocalSwapMask p q mask).2.Ice /\ sixVertexLocalCTypeCount p q <= sixVertexLocalCTypeCount (sixVertexLocalSwapMask p q mask).1 (sixVertexLocalSwapMask p q mask).2 /\ (sixVertexLocalSwitchMaskCount mask = 2 \/ sixVertexLocalSwitchMaskCount mask = 4) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexLocalSwapMask_of_disagreement p q d hp hq hd

/--
[sixVertexRectangleLocalIncomingPattern_pairSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexRectangleLocalIncomingPattern_pairSwitch_eq
  {mask omega eta : SixVertexRectangleArrows N M}
  {v : Fin N × Fin M} :
-- imply
  (sixVertexRectangleLocalIncomingPattern (sixVertexRectangleSwitchFirst mask omega eta) v, sixVertexRectangleLocalIncomingPattern (sixVertexRectangleSwitchSecond mask omega eta) v) = sixVertexLocalSwapMask (sixVertexRectangleLocalIncomingPattern omega v) (sixVertexRectangleLocalIncomingPattern eta v) (sixVertexRectangleLocalSwitchMask mask v) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleLocalIncomingPattern_pairSwitch mask omega eta v

/--
[sixVertexLocalSwapMask_eq_swapTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexLocalSwapMask_eq_swapTwo_eq
  {p q mask : SixVertexLocalIncomingPattern}
  {d e : Fin 4}
-- given
  (hmask : forall i, mask i = decide (i = d \/ i = e)) :
-- imply
  sixVertexLocalSwapMask p q mask = sixVertexLocalSwapTwo p q d e := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalSwapMask_eq_swapTwo p q mask d e hmask

/--
[sixVertexRectanglePairSwitch_weight_product_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexRectanglePairSwitch_weight_product_le_eq
  {c : Real}
  {mask omega eta : SixVertexRectangleArrows N M}
-- given
  (hc : 0 <= c)
  (hlocal : forall v, omega.localWeight c v * eta.localWeight c v <= (sixVertexRectangleSwitchFirst mask omega eta).localWeight c v * (sixVertexRectangleSwitchSecond mask omega eta).localWeight c v) :
-- imply
  omega.weight c * eta.weight c <= (sixVertexRectangleSwitchFirst mask omega eta).weight c * (sixVertexRectangleSwitchSecond mask omega eta).weight c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectanglePairSwitch_weight_product_le hc mask omega eta hlocal

/--
[sixVertexTorusLocalIncomingPattern_pairSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexTorusLocalIncomingPattern_pairSwitch_eq
  {mask omega eta : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  (sixVertexLocalIncomingPattern (sixVertexTorusSwitchFirst mask omega eta) v, sixVertexLocalIncomingPattern (sixVertexTorusSwitchSecond mask omega eta) v) = sixVertexLocalSwapMask (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v) (sixVertexTorusLocalSwitchMask mask v) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusLocalIncomingPattern_pairSwitch mask omega eta v


-- created on 2026-10-23
