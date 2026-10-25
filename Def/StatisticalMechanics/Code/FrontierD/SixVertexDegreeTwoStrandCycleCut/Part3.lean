/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut


namespace StatMech.FrontierD

noncomputable section

def sixVertexDegreeTwoStrandCycleForwardArc
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (cut : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed)))
    (hcut : 0 < cut.val) : SixVertexDirectedSimpleArc T := by
  let cycle := sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed
  refine {
    length := cut.val
    length_pos := hcut
    edge := fun i => cycle.edge (sixVertexFinPrefixIndex cut i)
    head_eq_next_tail := ?_
    tail_injective := ?_
    physical_injective := ?_ }
  · intro i
    have hnext := cycle.head_eq_next_tail
      (sixVertexFinPrefixIndex cut ⟨i.val, by omega⟩)
    rw [finitePeriodicSucc_prefixIndex cycle.length_pos cut i.val (by omega)] at hnext
    exact hnext
  · intro i j h
    apply sixVertexFinPrefixIndex_injective cut
    exact cycle.tail_injective h
  · intro i j h
    apply sixVertexFinPrefixIndex_injective cut
    exact cycle.physical_injective h


def sixVertexDegreeTwoStrandCycleBackwardArc
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (cut : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))) : SixVertexDirectedSimpleArc T := by
  let cycle := sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed
  refine {
    length := orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed) - cut.val
    length_pos := by
      omega
    edge := fun i => cycle.edge (sixVertexFinSuffixIndex cut i)
    head_eq_next_tail := ?_
    tail_injective := ?_
    physical_injective := ?_ }
  · intro i
    have hnext := cycle.head_eq_next_tail
      (sixVertexFinSuffixIndex cut ⟨i.val, by
        change i.val < orderOf (sixVertexDegreeTwoStrandCyclePerm
          homega heta hdegree seed) - cut.val
        omega⟩)
    rw [finitePeriodicSucc_suffixIndex cycle.length_pos cut i.val (by
      change i.val + 1 < orderOf (sixVertexDegreeTwoStrandCyclePerm
        homega heta hdegree seed) - cut.val
      omega)] at hnext
    exact hnext
  · intro i j h
    apply sixVertexFinSuffixIndex_injective cut
    exact cycle.tail_injective h
  · intro i j h
    apply sixVertexFinSuffixIndex_injective cut
    exact cycle.physical_injective h

end
end StatMech.FrontierD
