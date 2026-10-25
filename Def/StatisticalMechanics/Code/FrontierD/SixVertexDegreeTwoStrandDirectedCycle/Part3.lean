/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (length : Nat) (length_pos : 0 < length)
    (dart : Fin length → SixVertexOrientedDisagreementDart omega eta)
    (dart_injective : Function.Injective dart)
    (next : ∀ i, dart (finitePeriodicSucc length_pos i) =
      sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree (dart i)) :
    SixVertexDirectedSimpleCycle T where
  length := length
  length_pos := length_pos
  edge := fun i => sixVertexDegreeTwoOrientedStrandEdge hdegree (dart i)
  head_eq_next_tail := by
    intro i
    rw [sixVertexDegreeTwoOrientedStrandEdge_head homega heta hdegree,
      sixVertexDegreeTwoOrientedStrandEdge_tail homega heta hdegree,
      next i]
  tail_injective := by
    intro first second heq
    apply dart_injective
    apply sixVertexOrientedDisagreementDart_vertex_injective
      homega heta hdegree
    simpa only [sixVertexDegreeTwoOrientedStrandEdge_tail
      homega heta hdegree] using heq
  physical_injective := by
    intro first second heq
    apply dart_injective
    apply sixVertexDegreeTwoOrientedStrandEdge_physical_injective
      homega heta hdegree
    exact heq

end
end StatMech.FrontierD
