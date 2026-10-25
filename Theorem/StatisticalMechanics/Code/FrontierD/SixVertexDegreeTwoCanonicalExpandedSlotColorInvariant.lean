/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant


namespace StatMech.FrontierD

noncomputable section

theorem fkMedialTogglePairingAt_two_eq_toggleMask
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (first second : T.Vertex) (hne : first ≠ second) :
    fkMedialTogglePairingAt (fkMedialTogglePairingAt pairing first) second =
      fkMedialTogglePairingMask pairing
        (fun v => decide (v = first) || decide (v = second)) := by
  funext v
  by_cases hfirst : v = first <;> by_cases hsecond : v = second
  · exact False.elim (hne (hfirst.symm.trans hsecond))
  all_goals simp [fkMedialTogglePairingAt, fkMedialTogglePairingMask,
    hfirst, hsecond, hne, Ne.symm hne]

theorem sixVertexDegreeTwoAlignedTargetPairing_eq_toggleMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle
        homegaSector hetaSector hmiddle layer =
      fkMedialTogglePairingMask
        (alignedRoutingLoopPairing homega heta hdegree layer)
        (sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
          homegaSector hetaSector hmiddle) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  by_cases hleft : cut.cutLeft = []
  · rw [sixVertexDegreeTwoAlignedTargetPairing_of_left_empty homega heta
      hdegree middle homegaSector hetaSector hmiddle hleft]
    funext v
    simp [sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft,
      fkMedialTogglePairingMask]
  · by_cases hright : cut.cutRight = []
    · rw [sixVertexDegreeTwoAlignedTargetPairing_of_right_empty homega heta
        hdegree middle homegaSector hetaSector hmiddle hright]
      funext v
      simp [sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft, hright,
        fkMedialTogglePairingMask]
    · rw [sixVertexDegreeTwoAlignedTargetPairing_of_proper homega heta
        hdegree middle homegaSector hetaSector hmiddle hleft hright]
      by_cases hvertices : doubledAlignedVertex (cut.cutRight.head hright) =
          doubledAlignedVertex (cut.cutLeft.head hleft)
      · rw [sixVertexRetieAtTransitionVertices_of_eq _ hvertices]
        funext v
        simp [
          sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft, hright,
          fkMedialTogglePairingMask, fkMedialTogglePairingAt, hvertices]
      · rw [sixVertexRetieAtTransitionVertices_of_ne _ hvertices]
        rw [fkMedialTogglePairingAt_two_eq_toggleMask _ _ _ hvertices]
        funext v
        simp [
          sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft, hright,
          fkMedialTogglePairingMask, hvertices]

@[simp] theorem fkMedialTogglePairingMask_compose
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (first second : T.Vertex -> Bool) :
    fkMedialTogglePairingMask (fkMedialTogglePairingMask pairing first)
        second =
      fkMedialTogglePairingMask pairing (fun v => first v != second v) := by
  funext v
  cases hfirst : first v <;> cases hsecond : second v <;>
    simp [fkMedialTogglePairingMask, hfirst, hsecond]


end
end StatMech.FrontierD
