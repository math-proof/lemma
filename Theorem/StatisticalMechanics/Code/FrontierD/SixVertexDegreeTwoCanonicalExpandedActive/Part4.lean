/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedInactive
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part4


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDegreeTwoCanonicalExpandedOutputState_fst
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
      homegaSector hetaSector hmiddle layer x).1 = x.1 := by
  cases hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex x) <;>
    cases hparity : fkMedialVertexParity (doubledAlignedVertex x) <;>
    simp [sixVertexDegreeTwoCanonicalExpandedOutputState, hmask, hparity]

@[simp] theorem sixVertexDegreeTwoCanonicalExpandedOutputState_self
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x) = x := by
  cases hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex x) <;>
    cases hparity : fkMedialVertexParity (doubledAlignedVertex x) <;>
    simp [sixVertexDegreeTwoCanonicalExpandedOutputState, hmask, hparity]

theorem sixVertexDegreeTwoCanonicalExpandedOutputState_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (doubledAlignedBranchSwap x) =
      doubledAlignedBranchSwap
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x) := by
  cases hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex x) <;>
    cases hparity : fkMedialVertexParity (doubledAlignedVertex x) <;>
    simp [sixVertexDegreeTwoCanonicalExpandedOutputState, hmask, hparity]

theorem sixVertexDegreeTwoCanonicalExpandedOutputState_leftHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let left := cut.cutLeft.head hleft
    let mismatch :=
      (orientedDartAlignedRetie homega heta hdegree left.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree left.1).pairingQ
    sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer left =
      if !mismatch &&
          (fkMedialVertexParity (doubledAlignedVertex left) == true) then
        doubledAlignedBranchSwap left else left := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let left := cut.cutLeft.head hleft
  let mismatch :=
    (orientedDartAlignedRetie homega heta hdegree left.1).pairingP !=
      (orientedDartAlignedRetie homega heta hdegree left.1).pairingQ
  change (if sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
        middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex left) &&
        (fkMedialVertexParity (doubledAlignedVertex left) == true) then
      doubledAlignedBranchSwap left else left) = _
  rw [sixVertexDegreeTwoCanonicalExpandedRetieMask_leftHead homega heta hdegree
    middle homegaSector hetaSector hmiddle hleft hright layer]

theorem sixVertexDegreeTwoCanonicalExpandedOutputState_rightHead_of_coincident
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft))
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let right := cut.cutRight.head hright
    let mismatch :=
      (orientedDartAlignedRetie homega heta hdegree right.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree right.1).pairingQ
    sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer right =
      if !mismatch &&
          (fkMedialVertexParity (doubledAlignedVertex right) == true) then
        doubledAlignedBranchSwap right else right := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let right := cut.cutRight.head hright
  let mismatch :=
    (orientedDartAlignedRetie homega heta hdegree right.1).pairingP !=
      (orientedDartAlignedRetie homega heta hdegree right.1).pairingQ
  change (if sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
        middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex right) &&
        (fkMedialVertexParity (doubledAlignedVertex right) == true) then
      doubledAlignedBranchSwap right else right) = _
  rw [sixVertexDegreeTwoCanonicalExpandedRetieMask_rightHead_of_coincident
    homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
    hvertex layer]

end
end StatMech.FrontierD
