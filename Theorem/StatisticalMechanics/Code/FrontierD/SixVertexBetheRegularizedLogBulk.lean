/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogTaylor.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetConvergence
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateDecomposition
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogBulk


namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

theorem sum_even_symmetric_regularized
    (c epsilon : Real) (m : Nat) {p : Fin (m + m) -> Real}
    (hp : SixVertexRootSymmetric p) :
    (∑ i, sixVertexRegularizedBetheLogKernel c epsilon (p i)) =
      2 * ∑ j, sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenPositiveHalfProjection m p j) := by
  rw [<- sixVertexEvenSymmetricLift_projection m hp, Fin.sum_univ_add]
  have hneg :
      (∑ j : Fin m, sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenSymmetricLift m
          (sixVertexEvenPositiveHalfProjection m p) (Fin.castAdd m j))) =
      ∑ j : Fin m, sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenPositiveHalfProjection m p j) := by
    rw [show (∑ j : Fin m, sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenSymmetricLift m
          (sixVertexEvenPositiveHalfProjection m p) (Fin.castAdd m j))) =
      ∑ j : Fin m, sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenPositiveHalfProjection m p j.rev) by
      apply Finset.sum_congr rfl
      intro j _
      rw [sixVertexEvenSymmetricLift_castAdd]
      exact even_sixVertexRegularizedBetheLogKernel c epsilon _]
    simpa using (Equiv.sum_comp Fin.revPerm
      (fun j : Fin m => sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenPositiveHalfProjection m p j)))
  rw [hneg]
  simp only [sixVertexEvenSymmetricLift_natAdd,
    sixVertexEvenPositiveHalfProjection_lift]
  ring

theorem eventually_full_regularizedLogDisplacement_eq_two_positive
    {c : Real} (hc : 2 < c) (epsilon : Real) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      (∑ i, (sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i) -
        sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexCanonicalEvenAlignedHalfRoots hc s k i))) =
        2 * sixVertexCanonicalEvenRegularizedBulkLogDisplacement
          hc epsilon s k := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s]
      with k hk
  rw [Finset.sum_sub_distrib,
    sum_even_symmetric_regularized c epsilon (s + k + 1) hk.1.1.2.1,
    sum_even_symmetric_regularized c epsilon (s + k + 1)
      (fun j => sixVertexCanonicalEvenAlignedHalfRoots_rev hc s k j)]
  unfold sixVertexCanonicalEvenRegularizedBulkLogDisplacement
    sixVertexCanonicalFixedEvenDensityPositiveRoots
  have haligned (j : Fin (s + k + 1)) :
      sixVertexEvenPositiveHalfProjection (s + k + 1)
          (sixVertexCanonicalEvenAlignedHalfRoots hc s k) j =
        sixVertexCanonicalEvenCommonHalfRoot hc s k j := by
    rw [sixVertexEvenPositiveHalfProjection_apply,
      sixVertexCanonicalEvenAlignedHalfRoots_positive]
  simp_rw [haligned]
  rw [Finset.sum_sub_distrib]
  ring

end
end StatMech.FrontierD
