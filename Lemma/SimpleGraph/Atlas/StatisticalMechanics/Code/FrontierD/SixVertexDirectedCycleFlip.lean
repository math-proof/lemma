import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part6
open StatMech StatMech.FrontierD


/--
[sixVertexLocalFlipMask_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexLocalFlipMask_ice_eq
  {pattern mask : SixVertexLocalIncomingPattern}
-- given
  (hice : pattern.Ice)
  (hmask : sixVertexLocalSwitchMaskCount mask = 0 \/ (sixVertexLocalSwitchMaskCount mask = 2 /\ sixVertexLocalSelectedIncomingCount pattern mask = 1)) :
-- imply
  (sixVertexLocalFlipMask pattern mask).Ice := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalFlipMask_ice pattern mask hice hmask

/--
[sixVertexLocalSelectedIncomingCount_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexLocalSelectedIncomingCount_flip_eq
  {pattern mask : SixVertexLocalIncomingPattern}
-- given
  (htwo : sixVertexLocalSwitchMaskCount mask = 2)
  (hone : sixVertexLocalSelectedIncomingCount pattern mask = 1) :
-- imply
  sixVertexLocalSelectedIncomingCount (sixVertexLocalFlipMask pattern mask) mask = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalSelectedIncomingCount_flip pattern mask htwo hone

/--
[sixVertexLocalFlipMask_ice_of_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexLocalFlipMask_ice_of_balanced_eq
  {pattern mask : SixVertexLocalIncomingPattern}
-- given
  (hice : pattern.Ice)
  (hbalanced : SixVertexLocalBalancedFlipMask pattern mask) :
-- imply
  (sixVertexLocalFlipMask pattern mask).Ice := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalFlipMask_ice_of_balanced pattern mask hice hbalanced

/--
[SixVertexLocalBalancedFlipMask.after_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma after_flip_eq
  {pattern mask : SixVertexLocalIncomingPattern}
-- given
  (hbalanced : SixVertexLocalBalancedFlipMask pattern mask) :
-- imply
  SixVertexLocalBalancedFlipMask (sixVertexLocalFlipMask pattern mask) mask := by
-- proof
  apply StatMech.FrontierD.SixVertexLocalBalancedFlipMask.after_flip pattern mask hbalanced

/--
[sixVertexLocalBalancedFlipMask_of_ice_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexLocalBalancedFlipMask_of_ice_flip_eq
  {pattern mask : SixVertexLocalIncomingPattern}
-- given
  (hice : pattern.Ice)
  (hflip : (sixVertexLocalFlipMask pattern mask).Ice) :
-- imply
  SixVertexLocalBalancedFlipMask pattern mask := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalBalancedFlipMask_of_ice_flip pattern mask hice hflip

/--
[sixVertexLocalBalancedFlipMask_of_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexLocalBalancedFlipMask_of_cycle_eq
  {pattern mask : SixVertexLocalIncomingPattern}
-- given
  (hmask : sixVertexLocalSwitchMaskCount mask = 0 \/ (sixVertexLocalSwitchMaskCount mask = 2 /\ sixVertexLocalSelectedIncomingCount pattern mask = 1)) :
-- imply
  SixVertexLocalBalancedFlipMask pattern mask := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalBalancedFlipMask_of_cycle pattern mask hmask

/--
[sixVertexTorusFlip_maskXor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlip_maskXor_eq
  {T : EvenTorus}
  {first second omega : SixVertexArrows T} :
-- imply
  sixVertexTorusFlip second (sixVertexTorusFlip first omega) = sixVertexTorusFlip (sixVertexTorusMaskXor first second) omega := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlip_maskXor first second omega

/--
[sixVertexTorusFlip_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlip_self_eq
  {T : EvenTorus}
  {mask omega : SixVertexArrows T} :
-- imply
  sixVertexTorusFlip mask (sixVertexTorusFlip mask omega) = omega := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlip_self mask omega

/--
[sixVertexTorusFlip_horizontal_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlip_horizontal_selected_eq
  {T : EvenTorus}
  {mask omega : SixVertexArrows T}
  {edge : T.Vertex}
-- given
  (hselected : mask.horizontal edge = true) :
-- imply
  (sixVertexTorusFlip mask omega).horizontal edge = !omega.horizontal edge := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlip_horizontal_selected mask omega edge hselected

/--
[sixVertexTorusFlip_horizontal_unselected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlip_horizontal_unselected_eq
  {T : EvenTorus}
  {mask omega : SixVertexArrows T}
  {edge : T.Vertex}
-- given
  (hunselected : mask.horizontal edge = false) :
-- imply
  (sixVertexTorusFlip mask omega).horizontal edge = omega.horizontal edge := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlip_horizontal_unselected mask omega edge hunselected

/--
[sixVertexTorusFlip_vertical_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlip_vertical_selected_eq
  {T : EvenTorus}
  {mask omega : SixVertexArrows T}
  {edge : T.Vertex}
-- given
  (hselected : mask.vertical edge = true) :
-- imply
  (sixVertexTorusFlip mask omega).vertical edge = !omega.vertical edge := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlip_vertical_selected mask omega edge hselected

/--
[sixVertexTorusFlip_vertical_unselected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlip_vertical_unselected_eq
  {T : EvenTorus}
  {mask omega : SixVertexArrows T}
  {edge : T.Vertex}
-- given
  (hunselected : mask.vertical edge = false) :
-- imply
  (sixVertexTorusFlip mask omega).vertical edge = omega.vertical edge := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlip_vertical_unselected mask omega edge hunselected

/--
[sixVertexLocalIncomingPattern_torusFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexLocalIncomingPattern_torusFlip_eq
  {T : EvenTorus}
  {mask omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  sixVertexLocalIncomingPattern (sixVertexTorusFlip mask omega) v = sixVertexLocalFlipMask (sixVertexLocalIncomingPattern omega v) (sixVertexTorusLocalSwitchMask mask v) := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalIncomingPattern_torusFlip mask omega v

/--
[SixVertexDirectedCycleFlipMask.balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma balanced_eq
  {T : EvenTorus}
  {omega mask : SixVertexArrows T}
-- given
  (hmask : SixVertexDirectedCycleFlipMask omega mask) :
-- imply
  SixVertexBalancedFlipMask omega mask := by
-- proof
  apply StatMech.FrontierD.SixVertexDirectedCycleFlipMask.balanced hmask

/--
[sixVertexTorusFlip_ice_of_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlip_ice_of_balanced_eq
  {T : EvenTorus}
  {omega mask : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (hmask : SixVertexBalancedFlipMask omega mask) :
-- imply
  (sixVertexTorusFlip mask omega).IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlip_ice_of_balanced homega hmask

/--
[sixVertexBalancedFlipMask_of_ice_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexBalancedFlipMask_of_ice_flip_eq
  {T : EvenTorus}
  {omega mask : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (hflip : (sixVertexTorusFlip mask omega).IceRule) :
-- imply
  SixVertexBalancedFlipMask omega mask := by
-- proof
  apply StatMech.FrontierD.sixVertexBalancedFlipMask_of_ice_flip homega hflip

/--
[SixVertexBalancedFlipMask.maskXor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma maskXor_eq
  {T : EvenTorus}
  {omega first second : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (hfirst : SixVertexBalancedFlipMask omega first)
  (hsecond : SixVertexBalancedFlipMask (sixVertexTorusFlip first omega) second) :
-- imply
  SixVertexBalancedFlipMask omega (sixVertexTorusMaskXor first second) := by
-- proof
  apply StatMech.FrontierD.SixVertexBalancedFlipMask.maskXor homega hfirst hsecond

/--
[sixVertexTorusFlip_maskXor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlip_maskXor_eq_eq
  {T : EvenTorus}
  {first second omega : SixVertexArrows T} :
-- imply
  sixVertexTorusFlip (sixVertexTorusMaskXor first second) omega = sixVertexTorusFlip second (sixVertexTorusFlip first omega) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlip_maskXor_eq first second omega

/--
[SixVertexBalancedFlipMask.after_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma after_flip_eq_2
  {T : EvenTorus}
  {omega mask : SixVertexArrows T}
-- given
  (hmask : SixVertexBalancedFlipMask omega mask) :
-- imply
  SixVertexBalancedFlipMask (sixVertexTorusFlip mask omega) mask := by
-- proof
  apply StatMech.FrontierD.SixVertexBalancedFlipMask.after_flip hmask

/--
[sixVertexTorusFlip_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlip_ice_eq
  {T : EvenTorus}
  {omega mask : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (hmask : SixVertexDirectedCycleFlipMask omega mask) :
-- imply
  (sixVertexTorusFlip mask omega).IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlip_ice homega hmask

/--
[SixVertexDirectedCycleFlipMask.after_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma after_flip_eq_3
  {T : EvenTorus}
  {omega mask : SixVertexArrows T}
-- given
  (hmask : SixVertexDirectedCycleFlipMask omega mask) :
-- imply
  SixVertexDirectedCycleFlipMask (sixVertexTorusFlip mask omega) mask := by
-- proof
  apply StatMech.FrontierD.SixVertexDirectedCycleFlipMask.after_flip hmask

/--
[sixVertexTorusLocalSwitchMask_agreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusLocalSwitchMask_agreement_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  sixVertexTorusLocalSwitchMask (sixVertexTorusAgreementMask omega eta) v = sixVertexLocalAgreementMask (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusLocalSwitchMask_agreement omega eta v

/--
[sixVertexLocalAgreementMask_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexLocalAgreementMask_balanced_eq
  {first second : SixVertexLocalIncomingPattern}
-- given
  (hfirst : first.Ice)
  (hsecond : second.Ice)
  (hdegree : (sixVertexLocalDisagreementSides first second).card = 0 \/ (sixVertexLocalDisagreementSides first second).card = 2) :
-- imply
  SixVertexLocalBalancedFlipMask first (sixVertexLocalAgreementMask first second) := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalAgreementMask_balanced first second hfirst hsecond hdegree

/--
[sixVertexLocalAgreementMask_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexLocalAgreementMask_comm_eq
  {first second : SixVertexLocalIncomingPattern} :
-- imply
  sixVertexLocalAgreementMask first second = sixVertexLocalAgreementMask second first := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalAgreementMask_comm first second

/--
[sixVertexTorusAgreementMask_balanced_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusAgreementMask_balanced_first_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  SixVertexBalancedFlipMask omega (sixVertexTorusAgreementMask omega eta) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusAgreementMask_balanced_first homega heta hdegree

/--
[sixVertexTorusAgreementMask_balanced_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusAgreementMask_balanced_second_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  SixVertexBalancedFlipMask eta (sixVertexTorusAgreementMask omega eta) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusAgreementMask_balanced_second homega heta hdegree

/--
[sixVertexTorusFlip_agreement_ice_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlip_agreement_ice_first_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexTorusFlip (sixVertexTorusAgreementMask omega eta) omega).IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlip_agreement_ice_first homega heta hdegree

/--
[sixVertexTorusFlip_agreement_ice_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlip_agreement_ice_second_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexTorusFlip (sixVertexTorusAgreementMask omega eta) eta).IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlip_agreement_ice_second homega heta hdegree

/--
[sixVertexTorusFlip_upCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlip_upCount_eq
  {T : EvenTorus}
  {mask omega : SixVertexArrows T} :
-- imply
  (sixVertexUpCount (svTorusVerticalRows T (sixVertexTorusFlip mask omega) (svFinLast T.height_pos)) : Int) = (sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) : Int) + sixVertexTorusFlipSeamDelta mask omega := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlip_upCount mask omega

/--
[sixVertexTorusFlipSeamDelta_after_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlipSeamDelta_after_flip_eq
  {T : EvenTorus}
  {mask omega : SixVertexArrows T} :
-- imply
  sixVertexTorusFlipSeamDelta mask (sixVertexTorusFlip mask omega) = -sixVertexTorusFlipSeamDelta mask omega := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlipSeamDelta_after_flip mask omega

/--
[sixVertexTorusFlipSeamDelta_maskXor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlipSeamDelta_maskXor_eq
  {T : EvenTorus}
  {first second omega : SixVertexArrows T} :
-- imply
  sixVertexTorusFlipSeamDelta (sixVertexTorusMaskXor first second) omega = sixVertexTorusFlipSeamDelta first omega + sixVertexTorusFlipSeamDelta second (sixVertexTorusFlip first omega) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlipSeamDelta_maskXor first second omega


-- created on 2026-10-23
