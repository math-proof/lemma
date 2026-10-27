import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part9
open StatMech StatMech.FrontierD


/--
[sixVertexDegreeTwoCanonicalSelected_rightHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalSelected_rightHead_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle homegaSector hetaSector hmiddle (cut.cutRight.head hright) = false ∧ sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle homegaSector hetaSector hmiddle ((doubledAlignedFirstReturnPerm homega heta hdegree).symm (cut.cutRight.head hright)) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalSelected_rightHead homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright

/--
[sixVertexDegreeTwoCanonicalSelected_leftHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalSelected_leftHead_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle homegaSector hetaSector hmiddle (cut.cutLeft.head hleft) = true ∧ sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle homegaSector hetaSector hmiddle ((doubledAlignedFirstReturnPerm homega heta hdegree).symm (cut.cutLeft.head hleft)) = false := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalSelected_leftHead homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright

/--
[sixVertexDegreeTwoCanonicalTransitionMask_rightHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalTransitionMask_rightHead_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle homegaSector hetaSector hmiddle (doubledAlignedVertex (cut.cutRight.head hright)) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalTransitionMask_rightHead homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright

/--
[sixVertexDegreeTwoCanonicalTransitionMask_leftHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalTransitionMask_leftHead_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle homegaSector hetaSector hmiddle (doubledAlignedVertex (cut.cutLeft.head hleft)) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalTransitionMask_leftHead homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright

/--
[sixVertexDegreeTwoCanonicalTransitionMask_proper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalTransitionMask_proper_eq
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
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle homegaSector hetaSector hmiddle v = (decide (v = doubledAlignedVertex (cut.cutRight.head hright)) || decide (v = doubledAlignedVertex (cut.cutLeft.head hleft))) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalTransitionMask_proper homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright v

/--
[sixVertexDegreeTwoCanonicalSelectedVertex_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalSelectedVertex_of_mem_eq
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
  (hmiddle : 0 < middle)
  (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) :
-- imply
  sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle homegaSector hetaSector hmiddle (doubledAlignedVertex x) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalSelectedVertex_of_mem homega heta hdegree middle homegaSector hetaSector hmiddle x hx

/--
[sixVertexDegreeTwoCanonicalSelectedVertex_eq_membership](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalSelectedVertex_eq_membership_eq
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
  sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle homegaSector hetaSector hmiddle (doubledAlignedVertex x) = (decide (x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) || decide (doubledAlignedBranchSwap x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalSelectedVertex_eq_membership homega heta hdegree middle homegaSector hetaSector hmiddle x

/--
[sixVertexDegreeTwoCanonicalSelectedVertex_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalSelectedVertex_iff_eq
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
  sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle homegaSector hetaSector hmiddle (doubledAlignedVertex x) = true ↔ x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle ∨ doubledAlignedBranchSwap x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalSelectedVertex_iff homega heta hdegree middle homegaSector hetaSector hmiddle x

/--
[sixVertexDegreeTwoCanonicalExpandedRetieMask_activeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedRetieMask_activeState_eq
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
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer (doubledAlignedVertex x) = let transition := sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle homegaSector hetaSector hmiddle (doubledAlignedVertex x) let selected := (decide (x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) || decide (doubledAlignedBranchSwap x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle)) transition != ((transition && !selected) || (selected && ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP != (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ))) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedRetieMask_activeState homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoCanonicalSelectedVertex_leftHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalSelectedVertex_leftHead_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle homegaSector hetaSector hmiddle (doubledAlignedVertex (cut.cutLeft.head hleft)) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalSelectedVertex_leftHead homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright

/--
[sixVertexDegreeTwoCanonicalSelectedVertex_rightHead_of_coincident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalSelectedVertex_rightHead_of_coincident_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hvertex : doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright) = doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle homegaSector hetaSector hmiddle (doubledAlignedVertex (cut.cutRight.head hright)) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalSelectedVertex_rightHead_of_coincident homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex

/--
[sixVertexDegreeTwoCanonicalCorrectionMask_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalCorrectionMask_of_mem_eq
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
  (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) :
-- imply
  sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle homegaSector hetaSector hmiddle layer (doubledAlignedVertex x) = ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP != (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalCorrectionMask_of_mem homega heta hdegree middle homegaSector hetaSector hmiddle layer x hx

/--
[sixVertexDegreeTwoCanonicalExpandedRetieMask_leftHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedRetieMask_leftHead_eq
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
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let left := cut.cutLeft.head hleft sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer (doubledAlignedVertex left) = !((orientedDartAlignedRetie homega heta hdegree left.1).pairingP != (orientedDartAlignedRetie homega heta hdegree left.1).pairingQ) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedRetieMask_leftHead homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright layer

/--
[sixVertexDegreeTwoCanonicalExpandedRetieMask_rightHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedRetieMask_rightHead_eq
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
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let right := cut.cutRight.head hright let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle homegaSector hetaSector hmiddle (doubledAlignedVertex right) let mismatch := (orientedDartAlignedRetie homega heta hdegree right.1).pairingP != (orientedDartAlignedRetie homega heta hdegree right.1).pairingQ sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer (doubledAlignedVertex right) = (selected && !mismatch) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedRetieMask_rightHead homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright layer

/--
[sixVertexDegreeTwoCanonicalExpandedRetieMask_rightHead_of_coincident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedRetieMask_rightHead_of_coincident_eq
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
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hvertex : doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright) = doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let right := cut.cutRight.head hright sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer (doubledAlignedVertex right) = !((orientedDartAlignedRetie homega heta hdegree right.1).pairingP != (orientedDartAlignedRetie homega heta hdegree right.1).pairingQ) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedRetieMask_rightHead_of_coincident homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex layer

/--
[sixVertexDegreeTwoCanonicalTransportedColor_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalTransportedColor_active_eq
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
  (hmiddle : 0 < middle) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x)) = if sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle homegaSector hetaSector hmiddle x then fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (!layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree (!layer) x) else fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalTransportedColor_active homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoAlignedActiveColor_false_branchSwap_bne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedActiveColor_false_branchSwap_bne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x != sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false (doubledAlignedBranchSwap x)) = (sixVertexLocalIncomingPattern omega (doubledAlignedVertex x) 0 != sixVertexLocalIncomingPattern omega (doubledAlignedVertex x) 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedActiveColor_false_branchSwap_bne homega heta hdegree x

/--
[sixVertexDegreeTwoAlignedActiveColor_true_branchSwap_bne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedActiveColor_true_branchSwap_bne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true x != sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true (doubledAlignedBranchSwap x)) = (sixVertexLocalIncomingPattern eta (doubledAlignedVertex x) 0 != sixVertexLocalIncomingPattern eta (doubledAlignedVertex x) 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedActiveColor_true_branchSwap_bne homega heta hdegree x

/--
[sixVertexDegreeTwoCanonicalTransportedColor_rightHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalTransportedColor_rightHead_eq
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
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let head := cut.cutRight.head hright let predecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm head sixVertexDegreeTwoCanonicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle layer head = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer head ∧ sixVertexDegreeTwoCanonicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle layer predecessor = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree (!layer) predecessor := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalTransportedColor_rightHead homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright layer

/--
[sixVertexDegreeTwoCanonicalTransportedColor_leftHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalTransportedColor_leftHead_eq
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
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let head := cut.cutLeft.head hleft let predecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm head sixVertexDegreeTwoCanonicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle layer head = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree (!layer) head ∧ sixVertexDegreeTwoCanonicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle layer predecessor = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer predecessor := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalTransportedColor_leftHead homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright layer

/--
[fkMedialBlackDartMaskSwap_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma fkMedialBlackDartMaskSwap_vertex_eq
  {T : EvenTorus}
  {dart : FKMedialBlackDart T}
-- given
  (mask : T.Vertex -> Bool) :
-- imply
  (fkMedialBlackDartMaskSwap mask dart).1.1 = dart.1.1 := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackDartMaskSwap_vertex mask dart

/--
[activeBlackDart_maskSwap_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma activeBlackDart_maskSwap_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {dart : FKMedialBlackDart T}
-- given
  (mask : T.Vertex -> Bool) :
-- imply
  activeBlackDart (omega := omega) (eta := eta) (fkMedialBlackDartMaskSwap mask dart) ↔ activeBlackDart (omega := omega) (eta := eta) dart := by
-- proof
  apply StatMech.FrontierD.activeBlackDart_maskSwap_iff mask dart

/--
[finiteFirstReturn_togglePairingMask_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma finiteFirstReturn_togglePairingMask_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {pairing : FKMedialLoopPairing T}
  {dart : FKMedialBlackDart T}
-- given
  (mask : T.Vertex -> Bool)
  (hmask : forall (dart : FKMedialBlackDart T), Not (activeBlackDart (omega := omega) (eta := eta) dart) -> mask dart.1.1 = false)
  (hactive : activeBlackDart (omega := omega) (eta := eta) dart) :
-- imply
  let swapped := fkMedialBlackDartMaskSwap mask dart (finiteFirstReturn (fkMedialBlackBoundaryPerm (fkMedialTogglePairingMask pairing mask)) (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1 = (finiteFirstReturn (fkMedialBlackBoundaryPerm pairing) (activeBlackDart (omega := omega) (eta := eta)) ⟨swapped, (activeBlackDart_maskSwap_iff mask dart).mpr hactive⟩).1 := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturn_togglePairingMask_active pairing mask hmask dart hactive

/--
[sixVertexDegreeTwoCanonicalExpanded_firstReturn_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpanded_firstReturn_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hactive : activeBlackDart (omega := omega) (eta := eta) dart) :
-- imply
  let mask := sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer let swapped := fkMedialBlackDartMaskSwap mask dart (finiteFirstReturn (fkMedialBlackBoundaryPerm (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer)) (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1 = (finiteFirstReturn (alignedBoundaryPerm homega heta hdegree layer) (activeBlackDart (omega := omega) (eta := eta)) ⟨swapped, (activeBlackDart_maskSwap_iff mask dart).mpr hactive⟩).1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpanded_firstReturn_active homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hactive

/--
[fkMedialBlackDartMaskSwap_targetSlot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma fkMedialBlackDartMaskSwap_targetSlot_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {slot : T.Vertex × Bool}
-- given
  (mask : T.Vertex -> Bool) :
-- imply
  fkColoredBlackDartStrandSlotEquiv pairing (fkMedialBlackDartMaskSwap mask ((fkColoredBlackDartStrandSlotEquiv (fkMedialTogglePairingMask pairing mask)).symm slot)) = fkColoredParityMaskStrandSlotSwap mask false slot := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackDartMaskSwap_targetSlot pairing mask slot

/--
[fkMedialBlackDartMaskSwap_canonicalTargetState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma fkMedialBlackDartMaskSwap_canonicalTargetState_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (mask : T.Vertex -> Bool) :
-- imply
  fkMedialBlackDartMaskSwap mask ((fkColoredBlackDartStrandSlotEquiv (fkMedialTogglePairingMask (alignedRoutingLoopPairing homega heta hdegree layer) mask)).symm (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x)) = doubledAlignedBlackDart homega heta hdegree layer (if mask (doubledAlignedVertex x) && (fkMedialVertexParity (doubledAlignedVertex x) == false) then doubledAlignedBranchSwap x else x) := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackDartMaskSwap_canonicalTargetState homega heta hdegree mask layer x

/--
[fkColoredParityMaskStrandSlotSwap_doubledAlignedState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma fkColoredParityMaskStrandSlotSwap_doubledAlignedState_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {parity layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (mask : T.Vertex -> Bool) :
-- imply
  fkColoredParityMaskStrandSlotSwap mask parity (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x) = (doubledAlignedVertex (if mask (doubledAlignedVertex x) && (fkMedialVertexParity (doubledAlignedVertex x) == parity) then doubledAlignedBranchSwap x else x), doubledAlignedSlot homega heta hdegree layer (if mask (doubledAlignedVertex x) && (fkMedialVertexParity (doubledAlignedVertex x) == parity) then doubledAlignedBranchSwap x else x)) := by
-- proof
  apply StatMech.FrontierD.fkColoredParityMaskStrandSlotSwap_doubledAlignedState homega heta hdegree mask parity layer x

/--
[sixVertexDegreeTwoCanonicalExpandedInputState_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedInputState_fst_eq
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
  (hmiddle : 0 < middle) :
-- imply
  (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle layer x).1 = x.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedInputState_fst homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoCanonicalExpandedInputState_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedInputState_self_eq
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
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle layer (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle layer x) = x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedInputState_self homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoCanonicalExpandedInputState_branchSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedInputState_branchSwap_eq
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
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle layer (doubledAlignedBranchSwap x) = doubledAlignedBranchSwap (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle layer x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedInputState_branchSwap homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoCanonicalExpandedOutputState_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedOutputState_fst_eq
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
  (hmiddle : 0 < middle) :
-- imply
  (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer x).1 = x.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedOutputState_fst homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoCanonicalExpandedOutputState_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedOutputState_self_eq
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
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer x) = x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedOutputState_self homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoCanonicalExpandedOutputState_branchSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedOutputState_branchSwap_eq
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
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer (doubledAlignedBranchSwap x) = doubledAlignedBranchSwap (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedOutputState_branchSwap homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoCanonicalExpandedOutputState_leftHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedOutputState_leftHead_eq
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
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let left := cut.cutLeft.head hleft let mismatch := (orientedDartAlignedRetie homega heta hdegree left.1).pairingP != (orientedDartAlignedRetie homega heta hdegree left.1).pairingQ sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer left = if !mismatch && (fkMedialVertexParity (doubledAlignedVertex left) == true) then doubledAlignedBranchSwap left else left := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedOutputState_leftHead homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright layer

/--
[sixVertexDegreeTwoCanonicalExpandedOutputState_rightHead_of_coincident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedOutputState_rightHead_of_coincident_eq
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
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hvertex : doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright) = doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let right := cut.cutRight.head hright let mismatch := (orientedDartAlignedRetie homega heta hdegree right.1).pairingP != (orientedDartAlignedRetie homega heta hdegree right.1).pairingQ sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer right = if !mismatch && (fkMedialVertexParity (doubledAlignedVertex right) == true) then doubledAlignedBranchSwap right else right := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedOutputState_rightHead_of_coincident homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex layer

/--
[sixVertexDegreeTwoCanonicalExpandedActiveReturnState_eq_output](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedActiveReturnState_eq_output_eq
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
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree middle homegaSector hetaSector hmiddle layer x = sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer (sixVertexDegreeTwoCanonicalExpandedSourceReturnState homega heta hdegree layer (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle layer x)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedActiveReturnState_eq_output homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoCanonicalExpandedActiveReturnState_input](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedActiveReturnState_input_eq
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
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree middle homegaSector hetaSector hmiddle layer (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle layer x) = sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer (sixVertexDegreeTwoCanonicalExpandedSourceReturnState homega heta hdegree layer x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedActiveReturnState_input homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoCanonicalExpandedActiveReturnState_proper_false_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedActiveReturnState_proper_false_endpoints_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let rightHead := cut.cutRight.head hright let rightPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead let leftHead := cut.cutLeft.head hleft let leftPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree middle homegaSector hetaSector hmiddle false (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle false rightPredecessor) = sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle false rightHead ∧ sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree middle homegaSector hetaSector hmiddle false (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle false leftPredecessor) = sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle false leftHead := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedActiveReturnState_proper_false_endpoints homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright

/--
[sixVertexDegreeTwoCanonicalExpandedOutputState_coincident_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedOutputState_coincident_endpoints_eq
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
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hvertex : doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright) = doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer (cut.cutLeft.head hleft) = doubledAlignedBranchSwap (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer (cut.cutRight.head hright)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedOutputState_coincident_endpoints homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex layer

/--
[sixVertexDegreeTwoCanonicalExpandedActiveReturnState_coincident_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedActiveReturnState_coincident_endpoints_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hvertex : doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright) = doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let rightPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm (cut.cutRight.head hright) let leftPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm (cut.cutLeft.head hleft) sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree middle homegaSector hetaSector hmiddle false (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle false leftPredecessor) = doubledAlignedBranchSwap (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree middle homegaSector hetaSector hmiddle false (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle false rightPredecessor)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedActiveReturnState_coincident_endpoints homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex

/--
[sixVertexDegreeTwoCanonicalExpanded_firstReturn_slot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpanded_firstReturn_slot_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
  (hslot : fkColoredBlackDartStrandSlotEquiv (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) dart = (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x)) :
-- imply
  fkColoredBlackDartStrandSlotEquiv (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) ((finiteFirstReturn (fkMedialBlackBoundaryPerm (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer)) (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1) = (doubledAlignedVertex (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree middle homegaSector hetaSector hmiddle layer x), doubledAlignedSlot homega heta hdegree layer (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree middle homegaSector hetaSector hmiddle layer x)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpanded_firstReturn_slot homega heta hdegree middle homegaSector hetaSector hmiddle layer x dart hactive hslot

/--
[sixVertexDegreeTwoTauAdjustedState_trueDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoTauAdjustedState_trueDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  doubledAlignedBlackDart homega heta hdegree true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) = doubledAlignedBlackDart homega heta hdegree false x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoTauAdjustedState_trueDart homega heta hdegree x

/--
[sixVertexDegreeTwoTauAdjustedState_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoTauAdjustedState_fst_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x).1 = x.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoTauAdjustedState_fst homega heta hdegree x

/--
[sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (heq : (orientedDartAlignedRetie homega heta hdegree x.1).pairingP = (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) :
-- imply
  sixVertexDegreeTwoTauAdjustedState homega heta hdegree x = x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq homega heta hdegree x heq

/--
[sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hne : ¬(orientedDartAlignedRetie homega heta hdegree x.1).pairingP = (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) :
-- imply
  sixVertexDegreeTwoTauAdjustedState homega heta hdegree x = doubledAlignedBranchSwap x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne homega heta hdegree x hne

/--
[sixVertexDegreeTwoTauAdjustedState_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoTauAdjustedState_self_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoTauAdjustedState homega heta hdegree (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) = x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoTauAdjustedState_self homega heta hdegree x

/--
[sixVertexDegreeTwoTauAdjustedState_branchSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoTauAdjustedState_branchSwap_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoTauAdjustedState homega heta hdegree (doubledAlignedBranchSwap x) = doubledAlignedBranchSwap (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoTauAdjustedState_branchSwap homega heta hdegree x

/--
[sixVertexDegreeTwoCanonicalExpandedInputState_tauAdjusted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedInputState_tauAdjusted_eq
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
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle layer (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) = sixVertexDegreeTwoTauAdjustedState homega heta hdegree (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle layer x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedInputState_tauAdjusted homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoCanonicalExpandedOutputState_tauAdjusted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedOutputState_tauAdjusted_eq
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
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) = sixVertexDegreeTwoTauAdjustedState homega heta hdegree (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedOutputState_tauAdjusted homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoCanonicalPhysicalBoundaryKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalBoundaryKey_injective_eq
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
  Function.Injective (sixVertexDegreeTwoCanonicalPhysicalBoundaryKey homega heta hdegree middle homegaSector hetaSector hmiddle layer) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalBoundaryKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle layer

/--
[sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective_eq
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
  Function.Injective (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle layer) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle layer

/--
[sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_exists_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_exists_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  (∃ i, sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle layer i = fkColoredBlackDartStrandSlotEquiv (alignedRoutingLoopPairing homega heta hdegree layer) dart) ↔ dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_exists_iff homega heta hdegree middle homegaSector hetaSector hmiddle layer dart

/--
[sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle)) :
-- imply
  fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, fkColoredBlackDartStrandSlotEquiv (alignedRoutingLoopPairing homega heta hdegree layer) dart) = (!layer, fkColoredBlackDartStrandSlotEquiv (alignedRoutingLoopPairing homega heta hdegree (!layer)) dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hdart

/--
[sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart_of_not_mem_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle)) :
-- imply
  fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, fkColoredBlackDartStrandSlotEquiv (alignedRoutingLoopPairing homega heta hdegree layer) dart) = (layer, fkColoredBlackDartStrandSlotEquiv (alignedRoutingLoopPairing homega heta hdegree layer) dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart_of_not_mem homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hdart

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_falseDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_falseDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (false, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree false dart)) = if _hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) then fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (true, fkColoredBlackDartStrandSlotEquiv (alignedRoutingLoopPairing homega heta hdegree true) dart) else fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (false, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree false dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_falseDart homega heta hdegree middle homegaSector hetaSector hmiddle dart

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_trueDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_trueDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  let physical := alignedBlackDartLayerSwap homega heta hdegree dart fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (true, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree true dart)) = if _hphysical : physical ∈ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) then fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (false, fkColoredBlackDartStrandSlotEquiv (alignedRoutingLoopPairing homega heta hdegree false) physical) else fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (true, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree true dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_trueDart homega heta hdegree middle homegaSector hetaSector hmiddle dart

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_dart_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_dart_of_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) dart)) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_dart_of_inactive homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hinactive

/--
[sixVertexDegreeTwoCanonicalPhysicalExpanded_falseDart_color_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalExpanded_falseDart_color_of_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hdart : Not (activeBlackDart (omega := omega) (eta := eta) dart))
  (hnext : Not (activeBlackDart (omega := omega) (eta := eta) (alignedBoundaryPerm homega heta hdegree false dart))) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart))) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalExpanded_falseDart_color_of_inactive homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hdart hnext

/--
[sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState_eq
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
  (hmiddle : 0 < middle)
  (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) :
-- imply
  sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree middle homegaSector hetaSector hmiddle x hx) = (doubledAlignedVertex (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x), doubledAlignedSlot homega heta hdegree true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState homega heta hdegree middle homegaSector hetaSector hmiddle x hx

/--
[sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState_false_eq
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
  (hmiddle : 0 < middle)
  (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) :
-- imply
  sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle false (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree middle homegaSector hetaSector hmiddle x hx) = (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree false x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState_false homega heta hdegree middle homegaSector hetaSector hmiddle x hx

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_activeDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_activeDart_eq
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
  (hmiddle : 0 < middle) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (doubledAlignedBlackDart homega heta hdegree false x))) = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle layer x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_activeDart homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_firstReturn_slot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_firstReturn_slot_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
  (hslot : fkColoredBlackDartStrandSlotEquiv (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) dart = (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x)) :
-- imply
  let arrival := (finiteFirstReturn (fkMedialBlackBoundaryPerm (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer)) (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1 fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, fkColoredBlackDartStrandSlotEquiv (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) arrival)) = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle layer (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree middle homegaSector hetaSector hmiddle layer x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_firstReturn_slot homega heta hdegree middle homegaSector hetaSector hmiddle layer x dart hactive hslot

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_targetStart_slot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_targetStart_slot_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hslot : fkColoredBlackDartStrandSlotEquiv (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) dart = (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x)) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, fkColoredBlackDartStrandSlotEquiv (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) dart)) = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle layer x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_targetStart_slot homega heta hdegree middle homegaSector hetaSector hmiddle layer x dart hslot

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_firstReturn_of_activeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_firstReturn_of_activeState_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
  (hslot : fkColoredBlackDartStrandSlotEquiv (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) dart = (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x))
  (hcolor : sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle layer (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree middle homegaSector hetaSector hmiddle layer x) = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle layer x) :
-- imply
  let arrival := (finiteFirstReturn (fkMedialBlackBoundaryPerm (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer)) (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1 fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, fkColoredBlackDartStrandSlotEquiv (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) arrival)) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, fkColoredBlackDartStrandSlotEquiv (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) dart)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_firstReturn_of_activeState homega heta hdegree middle homegaSector hetaSector hmiddle layer x dart hactive hslot hcolor

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_false_eq
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
  (hmiddle : 0 < middle)
  (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) :
-- imply
  sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle false x = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_false homega heta hdegree middle homegaSector hetaSector hmiddle x hx

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_true_eq
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
  (hmiddle : 0 < middle)
  (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) :
-- imply
  sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_true homega heta hdegree middle homegaSector hetaSector hmiddle x hx

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_false_eq
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
  (hmiddle : 0 < middle)
  (hx : x ∉ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) :
-- imply
  sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle false x = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_false homega heta hdegree middle homegaSector hetaSector hmiddle x hx

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_true_eq
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
  (hmiddle : 0 < middle)
  (hx : x ∉ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) :
-- imply
  sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_true homega heta hdegree middle homegaSector hetaSector hmiddle x hx

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_false_eq
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
  sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle false x = if _hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle then sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_false homega heta hdegree middle homegaSector hetaSector hmiddle x

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_true_eq
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
  sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle true x = if _hx : sixVertexDegreeTwoTauAdjustedState homega heta hdegree x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle then sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_true homega heta hdegree middle homegaSector hetaSector hmiddle x

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_true_tauAdjusted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_true_tauAdjusted_eq
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
  sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) = if _hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle then sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_true_tauAdjusted homega heta hdegree middle homegaSector hetaSector hmiddle x

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_input_false_defect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_input_false_defect_eq
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
  (hmiddle : 0 < middle)
  (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle)
  (htransition : sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle homegaSector hetaSector hmiddle (doubledAlignedVertex x) = false)
  (hpairing : (orientedDartAlignedRetie homega heta hdegree x.1).pairingP = (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) :
-- imply
  (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x != sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle false (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle false x)) = !x.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_input_false_defect homega heta hdegree middle homegaSector hetaSector hmiddle x hx htransition hpairing

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_rightHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_rightHead_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let head := cut.cutRight.head hright let predecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm head sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle false head = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false head ∧ sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle false predecessor = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree predecessor) ∧ sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree head) = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree head) ∧ sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree predecessor) = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false predecessor := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_rightHead homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_leftHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_leftHead_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let head := cut.cutLeft.head hleft let predecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm head sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle false head = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree head) ∧ sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle false predecessor = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false predecessor ∧ sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree head) = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false head ∧ sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree predecessor) = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree predecessor) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_leftHead homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_endpoint_false_stitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_endpoint_false_stitch_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let rightHead := cut.cutRight.head hright let rightPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead let leftHead := cut.cutLeft.head hleft let leftPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree rightPredecessor) = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle false rightHead ∧ sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle false leftPredecessor = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree leftHead) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_endpoint_false_stitch homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright

/--
[sixVertexDegreeTwoCanonicalPhysicalTransportedColor_endpoint_false_network](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalTransportedColor_endpoint_false_network_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let rightHead := cut.cutRight.head hright let rightPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead let leftHead := cut.cutLeft.head hleft let leftPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead let common := sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle false rightHead common = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree rightPredecessor) ∧ common = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle false leftPredecessor ∧ common = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree leftHead) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalTransportedColor_endpoint_false_network homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright

/--
[sixVertexDegreeTwoCanonicalExpandedTargetPairing_rightHead_table](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedTargetPairing_rightHead_table_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let v := doubledAlignedVertex (cut.cutRight.head hright) let hactive : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedTargetPairing_rightHead_table homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright

/--
[sixVertexDegreeTwoCanonicalExpandedTargetPairing_leftHead_table](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedTargetPairing_leftHead_table_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let v := doubledAlignedVertex (cut.cutLeft.head hleft) let hactive : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedTargetPairing_leftHead_table homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright

/--
[sixVertexDegreeTwoCanonicalCoincidentEndpoint_sourceColors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalCoincidentEndpoint_sourceColors_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hvertex : doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright) = doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let right := cut.cutRight.head hright let left := cut.cutLeft.head hleft left = doubledAlignedBranchSwap right ∧ sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false right = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false left ∧ (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true right != sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true left) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalCoincidentEndpoint_sourceColors homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex

/--
[sixVertexDegreeTwoCanonicalCoincidentEndpoint_outputSourceColors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalCoincidentEndpoint_outputSourceColors_eq
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
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hvertex : doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright) = doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let rightOut := sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer (cut.cutRight.head hright) let leftOut := sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle layer (cut.cutLeft.head hleft) sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false rightOut = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false leftOut ∧ (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true rightOut != sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true leftOut) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalCoincidentEndpoint_outputSourceColors homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex layer

/--
[sixVertexDegreeTwoCanonicalCoincidentEndpoint_activeReturnSourceColors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalCoincidentEndpoint_activeReturnSourceColors_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hvertex : doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright) = doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let rightPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm (cut.cutRight.head hright) let leftPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm (cut.cutLeft.head hleft) let rightReturn := sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree middle homegaSector hetaSector hmiddle false (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle false rightPredecessor) let leftReturn := sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree middle homegaSector hetaSector hmiddle false (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle false leftPredecessor) sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false rightReturn = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false leftReturn ∧ (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true rightReturn != sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true leftReturn) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalCoincidentEndpoint_activeReturnSourceColors homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex

/--
[sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_sigma_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_sigma_of_mem_eq
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
  (hmiddle : 0 < middle)
  (hy : doubledAlignedFirstReturnPerm homega heta hdegree x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) :
-- imply
  sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree middle homegaSector hetaSector hmiddle (doubledAlignedFirstReturnPerm homega heta hdegree x) hy) = (doubledAlignedVertex (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x), doubledAlignedSlot homega heta hdegree true (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_sigma_of_mem homega heta hdegree middle homegaSector hetaSector hmiddle x hy

/--
[sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_proper_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_proper_interior_eq
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
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle)
  (hexit : x ≠ (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.getLast hleft) :
-- imply
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x ∃ hy : y ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle, sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree middle homegaSector hetaSector hmiddle y hy) = (doubledAlignedVertex (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x), doubledAlignedSlot homega heta hdegree true (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_proper_interior homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright x hx hexit

/--
[sixVertexDegreeTwoAlignedTrueFirstReturnState_eq_tauAdjusted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedTrueFirstReturnState_eq_tauAdjusted_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x = sixVertexDegreeTwoTauAdjustedState homega heta hdegree (doubledAlignedFirstReturnPerm homega heta hdegree x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedTrueFirstReturnState_eq_tauAdjusted homega heta hdegree x

/--
[sixVertexDegreeTwoCanonicalExpandedActiveReturnState_proper_true_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedActiveReturnState_proper_true_endpoints_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ []) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle let rightHead := cut.cutRight.head hright let rightPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead let leftHead := cut.cutLeft.head hleft let leftPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle true rightPredecessor) = sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree rightHead) ∧ sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle homegaSector hetaSector hmiddle true leftPredecessor) = sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoTauAdjustedState homega heta hdegree leftHead) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedActiveReturnState_proper_true_endpoints homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright

/--
[sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_emptyCut_sigma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_emptyCut_sigma_eq
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
  (hmiddle : 0 < middle)
  (hempty : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft = [] \/ (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight = [])
  (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) :
-- imply
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x ∃ hy : y ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle, sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle true (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree middle homegaSector hetaSector hmiddle y hy) = (doubledAlignedVertex (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x), doubledAlignedSlot homega heta hdegree true (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_emptyCut_sigma homega heta hdegree middle homegaSector hetaSector hmiddle hempty x hx

/--
[sixVertexDegreeTwoCanonicalPhysicalExpandedSlotColorInvariant_of_falseDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalPhysicalExpandedSlotColorInvariant_of_falseDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hfalseDart : forall (layer : Bool) (dart : FKMedialBlackDart T), fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart))) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart))) :
-- imply
  FKColoredIndexedOccurrenceSlotColorInvariant (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle) (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalPhysicalExpandedSlotColorInvariant_of_falseDart homega heta hdegree middle homegaSector hetaSector hmiddle hfalseDart


-- created on 2026-10-23
