import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
open StatMech StatMech.FrontierD


/--
[sixVertexDegreeTwoBranchClosedUnitPrefix_tauAdjusted_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedUnitPrefix_tauAdjusted_mem_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoTauAdjustedState homega heta hdegree x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle ↔ x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedUnitPrefix_tauAdjusted_mem_iff homega heta hdegree middle homegaSector hetaSector hmiddle x

/--
[sixVertexDegreeTwoBranchClosed_unsynchronized_no_vertex_mask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosed_unsynchronized_no_vertex_mask_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {d : SixVertexOrientedDisagreementDart omega eta}
  {mask : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hunsync : ¬ sixVertexDegreeTwoBranchClosedSynchronizedAt homega heta hdegree middle homegaSector hetaSector hmiddle d) :
-- imply
  (mask != sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree middle homegaSector hetaSector hmiddle (d, false)) = true \/ (mask != sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree middle homegaSector hetaSector hmiddle (d, true)) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosed_unsynchronized_no_vertex_mask homega heta hdegree middle homegaSector hetaSector hmiddle d hunsync mask

/--
[sixVertexDegreeTwoBranchClosedExpandedRetieMask_misses_transition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedExpandedRetieMask_misses_transition_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {d : SixVertexOrientedDisagreementDart omega eta}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hunsync : ¬ sixVertexDegreeTwoBranchClosedSynchronizedAt homega heta hdegree middle homegaSector hetaSector hmiddle d) :
-- imply
  ∃ branch : Bool, (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer d.1.1.1 != sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree middle homegaSector hetaSector hmiddle (d, branch)) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedExpandedRetieMask_misses_transition homega heta hdegree middle homegaSector hetaSector hmiddle d hunsync layer

/--
[sixVertexDegreeTwoBranchClosedTransitionVertex_eq_bit_of_synchronized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedTransitionVertex_eq_bit_of_synchronized_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {d : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hsync : sixVertexDegreeTwoBranchClosedSynchronizedAt homega heta hdegree middle homegaSector hetaSector hmiddle d) :
-- imply
  sixVertexDegreeTwoBranchClosedTransitionVertex homega heta hdegree middle homegaSector hetaSector hmiddle d.1.1.1 = sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree middle homegaSector hetaSector hmiddle (d, false) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedTransitionVertex_eq_bit_of_synchronized homega heta hdegree middle homegaSector hetaSector hmiddle d hsync

/--
[sixVertexDegreeTwoBranchClosedPhysicalRetieMask_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedPhysicalRetieMask_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hzero : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 0) :
-- imply
  sixVertexDegreeTwoBranchClosedPhysicalRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer v = false := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedPhysicalRetieMask_inactive homega heta hdegree middle homegaSector hetaSector hmiddle layer v hzero

/--
[sixVertexDegreeTwoBranchClosedPhysicalBoundaryKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedPhysicalBoundaryKey_injective_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  Function.Injective (sixVertexDegreeTwoBranchClosedPhysicalBoundaryKey homega heta hdegree middle homegaSector hetaSector hmiddle layer) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedPhysicalBoundaryKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle layer

/--
[sixVertexDegreeTwoBranchClosedPhysicalBoundaryFinKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedPhysicalBoundaryFinKey_injective_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  Function.Injective (sixVertexDegreeTwoBranchClosedPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle layer) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle layer

/--
[sixVertexDegreeTwoBranchClosedPhysicalFinKey_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedPhysicalFinKey_selected_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hx : x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle) :
-- imply
  sixVertexDegreeTwoBranchClosedPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle layer (sixVertexDegreeTwoBranchClosedSelectedStateFinIndex homega heta hdegree middle homegaSector hetaSector hmiddle x hx) = if layer then (doubledAlignedVertex (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x), doubledAlignedSlot homega heta hdegree true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x)) else (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree false x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedPhysicalFinKey_selected homega heta hdegree middle homegaSector hetaSector hmiddle layer x hx

/--
[sixVertexDegreeTwoBranchClosedPhysicalTargetPairing_noTransition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedPhysicalTargetPairing_noTransition_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hactive : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 2)
  (htransition : sixVertexDegreeTwoBranchClosedTransitionVertex homega heta hdegree middle homegaSector hetaSector hmiddle v = false)
  (hselected : sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle homegaSector hetaSector hmiddle (orientedDisagreementDartAtActiveVertex homega heta v hactive, false) = true) :
-- imply
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive let retie := orientedDartAlignedRetie homega heta hdegree d (sixVertexDegreeTwoBranchClosedPhysicalTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle false v, sixVertexDegreeTwoBranchClosedPhysicalTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle true v) = (retie.pairingQ, retie.pairingP) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedPhysicalTargetPairing_noTransition homega heta hdegree middle homegaSector hetaSector hmiddle v hactive htransition hselected


-- created on 2026-10-23
