/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoStrandCycleForward_finish_eq_backward_start
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (cut : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))) (hcut : 0 < cut.val) :
    (sixVertexDegreeTwoStrandCycleForwardArc
      homega heta hdegree seed cut hcut).finish =
      (sixVertexDegreeTwoStrandCycleBackwardArc
        homega heta hdegree seed cut).start := by
  let cycle := sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed
  have hcutLtCycle : cut.val < cycle.length := by
    change cut.val < orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed)
    exact cut.isLt
  change (cycle.edge (sixVertexFinPrefixIndex cut
      ⟨cut.val - 1, by omega⟩)).head =
    (cycle.edge (sixVertexFinSuffixIndex cut ⟨0, by
      omega⟩)).tail
  have hnext := cycle.head_eq_next_tail
    (sixVertexFinPrefixIndex cut ⟨cut.val - 1, by omega⟩)
  rw [show finitePeriodicSucc cycle.length_pos
      (sixVertexFinPrefixIndex cut ⟨cut.val - 1, by omega⟩) =
        sixVertexFinSuffixIndex cut ⟨0, by
          change 0 < orderOf (sixVertexDegreeTwoStrandCyclePerm
            homega heta hdegree seed) - cut.val
          omega⟩ by
      apply Fin.ext
      change (cut.val - 1 + 1) %
        orderOf (sixVertexDegreeTwoStrandCyclePerm
          homega heta hdegree seed) = cut.val + 0
      rw [Nat.mod_eq_of_lt]
      · omega
      · omega] at hnext
  exact hnext

theorem sixVertexDegreeTwoStrandCycleBackward_finish_eq_forward_start
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (cut : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))) (hcut : 0 < cut.val) :
    (sixVertexDegreeTwoStrandCycleBackwardArc
      homega heta hdegree seed cut).finish =
      (sixVertexDegreeTwoStrandCycleForwardArc
        homega heta hdegree seed cut hcut).start := by
  let cycle := sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed
  change (cycle.edge (sixVertexFinSuffixIndex cut
      ⟨cycle.length - cut.val - 1, by
        change orderOf (sixVertexDegreeTwoStrandCyclePerm
          homega heta hdegree seed) - cut.val - 1 <
            orderOf (sixVertexDegreeTwoStrandCyclePerm
              homega heta hdegree seed) - cut.val
        omega⟩)).head =
    (cycle.edge (sixVertexFinPrefixIndex cut ⟨0, hcut⟩)).tail
  have hnext := cycle.head_eq_next_tail
    (sixVertexFinSuffixIndex cut
      ⟨cycle.length - cut.val - 1, by
        change orderOf (sixVertexDegreeTwoStrandCyclePerm
          homega heta hdegree seed) - cut.val - 1 <
            orderOf (sixVertexDegreeTwoStrandCyclePerm
              homega heta hdegree seed) - cut.val
        omega⟩)
  rw [show finitePeriodicSucc cycle.length_pos
      (sixVertexFinSuffixIndex cut
        ⟨cycle.length - cut.val - 1, by
          change orderOf (sixVertexDegreeTwoStrandCyclePerm
            homega heta hdegree seed) - cut.val - 1 <
              orderOf (sixVertexDegreeTwoStrandCyclePerm
                homega heta hdegree seed) - cut.val
          omega⟩) =
        sixVertexFinPrefixIndex cut ⟨0, hcut⟩ by
      apply Fin.ext
      change (cut.val + (cycle.length - cut.val - 1) + 1) % cycle.length = 0
      have hcutLt : cut.val < cycle.length := by
        exact cut.isLt
      have hlengthPos := cycle.length_pos
      have heq : cut.val + (cycle.length - cut.val - 1) + 1 =
          cycle.length := by omega
      rw [heq, Nat.mod_self]] at hnext
  exact hnext


end
end StatMech.FrontierD
