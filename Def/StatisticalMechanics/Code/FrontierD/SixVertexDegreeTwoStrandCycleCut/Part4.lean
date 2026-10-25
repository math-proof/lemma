/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexDegreeTwoStrandCycleComplementaryArcPair
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (cut : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed)))
    (hcut : 0 < cut.val) : SixVertexDirectedComplementaryArcPair T where
  first := sixVertexDegreeTwoStrandCycleForwardArc
    homega heta hdegree seed cut hcut
  second := sixVertexDegreeTwoStrandCycleBackwardArc
    homega heta hdegree seed cut
  first_finish_eq_second_start :=
    sixVertexDegreeTwoStrandCycleForward_finish_eq_backward_start
      homega heta hdegree seed cut hcut
  second_finish_eq_first_start :=
    sixVertexDegreeTwoStrandCycleBackward_finish_eq_forward_start
      homega heta hdegree seed cut hcut
  tail_disjoint := by
    intro i j htail
    let cycle := sixVertexDegreeTwoStrandDirectedSimpleCycle
      homega heta hdegree seed
    apply sixVertexFinPrefixIndex_ne_suffixIndex cut i j
    exact cycle.tail_injective htail
  physical_disjoint := by
    intro i j hphysical
    let cycle := sixVertexDegreeTwoStrandDirectedSimpleCycle
      homega heta hdegree seed
    apply sixVertexFinPrefixIndex_ne_suffixIndex cut i j
    exact cycle.physical_injective hphysical

end
end StatMech.FrontierD
