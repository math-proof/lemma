/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianStability.Part4
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricJacobian.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPositiveHalfRootGap_pos
    {m : Nat} {q : Fin m → Real} (hqmono : StrictMono q)
    (hqpos : ∀ k, 0 < q k) (k : Fin m) :
    0 < sixVertexPositiveHalfRootGap q k := by
  unfold sixVertexPositiveHalfRootGap
  split_ifs with hk
  · nlinarith [hqpos k]
  · let kp : Fin m := ⟨k.val - 1, by omega⟩
    have hpred : kp < k := by
      rw [Fin.lt_def]
      dsimp [kp]
      omega
    change 0 < q k - q kp
    linarith [hqmono hpred]

theorem sixVertexEvenSymmetricLift_positive_strictMono
    {m : Nat} {q : Fin m → Real}
    (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q)) :
    StrictMono q := by
  intro j k hjk
  have hidx : Fin.natAdd m j < Fin.natAdd m k := by
    rw [Fin.lt_def]
    simp [Fin.natAdd]
    omega
  simpa only [sixVertexEvenSymmetricLift_natAdd] using hq.1 hidx

theorem sixVertexPositiveHalfRootGap_pos_of_open
    {m : Nat} {q : Fin m → Real}
    (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (k : Fin m) : 0 < sixVertexPositiveHalfRootGap q k := by
  apply sixVertexPositiveHalfRootGap_pos
    (sixVertexEvenSymmetricLift_positive_strictMono hq)
  intro j
  exact (sixVertexEvenSymmetricLift_positive_mem_Icc hq j).1.lt_of_ne
    (fun h => by
      have hneg : -q j = 0 := by linarith
      let i : Fin (m + m) := Fin.natAdd m j
      let ir : Fin (m + m) := Fin.castAdd m j.rev
      have heq : sixVertexEvenSymmetricLift m q ir =
          sixVertexEvenSymmetricLift m q i := by
        rw [show sixVertexEvenSymmetricLift m q ir = -q j by
          change sixVertexEvenSymmetricLift m q (Fin.castAdd m j.rev) = -q j
          rw [sixVertexEvenSymmetricLift_castAdd]
          simp]
        rw [show sixVertexEvenSymmetricLift m q i = q j by
          exact sixVertexEvenSymmetricLift_natAdd m q j]
        linarith
      have hind : ir = i := hq.1.injective heq
      have hne : ir ≠ i := by
        intro hieq
        have hval := congrArg Fin.val hieq
        simp [i, ir, Fin.natAdd, Fin.castAdd] at hval
        omega
      exact hne hind)


end
end StatMech.FrontierD
