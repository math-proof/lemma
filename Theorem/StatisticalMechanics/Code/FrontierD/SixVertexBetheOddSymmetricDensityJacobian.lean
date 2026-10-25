/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricJacobian
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricDensityJacobian
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexOddSymmetricLift_positive_mem_Icc
    {m : Nat} {q : Fin m → Real}
    (hq : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    (j : Fin m) : q j ∈ Set.Icc 0 Real.pi := by
  let i := sixVertexOddPositiveIndex m j
  let z := sixVertexOddCentralIndex m
  have hzi : z < i := by
    rw [Fin.lt_def]
    simp [z, i, sixVertexOddCentralIndex, sixVertexOddPositiveIndex]
    omega
  have hpos : 0 < q j := by
    have hlt := hq.1 hzi
    change sixVertexOddSymmetricLift m q z <
      sixVertexOddSymmetricLift m q i at hlt
    rw [sixVertexOddSymmetricLift_central,
      sixVertexOddSymmetricLift_positive] at hlt
    exact hlt
  have hpi := (hq.2.2 i).2.le
  change sixVertexOddSymmetricLift m q i ≤ Real.pi at hpi
  rw [sixVertexOddSymmetricLift_positive] at hpi
  exact ⟨hpos.le, hpi⟩

theorem sixVertexOddPositiveHalfRootGap_pos_of_open
    {m : Nat} {q : Fin m → Real}
    (hq : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    (k : Fin m) : 0 < sixVertexOddPositiveHalfRootGap q k := by
  unfold sixVertexOddPositiveHalfRootGap
  split_ifs with hk
  · exact (sixVertexOddSymmetricLift_positive_mem_Icc hq k).1.lt_of_ne
      (fun h => by
        have := hq.1 (show sixVertexOddCentralIndex m <
          sixVertexOddPositiveIndex m k by
            rw [Fin.lt_def]
            simp [sixVertexOddCentralIndex, sixVertexOddPositiveIndex]
            omega)
        rw [sixVertexOddSymmetricLift_central,
          sixVertexOddSymmetricLift_positive, h] at this
        exact (lt_irrefl (q k) this).elim)
  · let kp : Fin m := ⟨k.val - 1, by omega⟩
    have hindex : sixVertexOddPositiveIndex m kp <
        sixVertexOddPositiveIndex m k := by
      rw [Fin.lt_def]
      simp [sixVertexOddPositiveIndex, kp]
      omega
    have hlt := hq.1 hindex
    rw [sixVertexOddSymmetricLift_positive,
      sixVertexOddSymmetricLift_positive] at hlt
    exact sub_pos.mpr hlt

end
end StatMech.FrontierD
