/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part28
open StatMech.FrontierD


namespace StatMech.FrontierD

theorem exists_canonicalDoubledAlignedOrbitChunkCut
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    let split := canonicalDoubledAlignedUnitOrbitSplit
      homega heta hdegree n homegaSector hetaSector hn
    exists before cut after cutLeft cutRight,
      alignedPermOrderedAllOrbitLists
          (doubledAlignedFirstReturnPerm homega heta hdegree) =
        before ++ cut :: after /\
      cut = cutLeft ++ cutRight /\
      split.first = before.flatten ++ cutLeft /\
      split.second = cutRight ++ after.flatten := by
  let split := canonicalDoubledAlignedUnitOrbitSplit
    homega heta hdegree n homegaSector hetaSector hn
  have hfirst : split.first ≠ [] := by
    intro hnil
    have hcharge := split.first_charge
    rw [hnil] at hcharge
    simp at hcharge
  have hall : alignedPermOrderedAllOrbits
      (doubledAlignedFirstReturnPerm homega heta hdegree) ≠ [] := by
    rw [split.split]
    intro hnil
    have := congrArg List.length hnil
    simp only [List.length_nil, List.length_append] at this
    have : split.first.length = 0 := by omega
    exact hfirst (List.length_eq_zero_iff.mp this)
  exact exists_aligned_orbit_chunk_cut
    (doubledAlignedFirstReturnPerm homega heta hdegree)
    split.first split.second split.split hall

end StatMech.FrontierD
