/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLogRegularizationCutoff
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalRegularizedQuadrature
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalLogUnregularization


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem eventually_abs_sixVertexCanonicalEvenBulkLogDisplacement_sub_regularized_le
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (s : Nat) {M : Nat} (hM : 0 < M) :
    ∀ᶠ k : Nat in atTop,
      let N := sixVertexFourWidth (2 * s) k
      let C := sixVertexCanonicalEvenOffsetLinearBound c hc s
      |sixVertexCanonicalEvenBulkLogDisplacement hc s k -
          sixVertexCanonicalEvenRegularizedBulkLogDisplacement
            hc epsilon s k| <=
        2 * Real.pi * C * (1 / M + 1 / N) +
          epsilon * C * Real.pi * M ^ 4 / 16 := by
  filter_upwards
    [eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_le_simple
      hc hepsilon s hM,
      eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness
        hc s] with k hk hfixed
  let n := s + k + 1
  let q : Fin n -> Real :=
    sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k
  let p : Fin n -> Real := sixVertexCanonicalEvenCommonHalfRoot hc s k
  have hq (j : Fin n) : q j ∈ Set.Ioo 0 Real.pi := by
    apply sixVertexEvenSymmetricLift_positive_mem_Ioo
    unfold q sixVertexCanonicalFixedEvenDensityPositiveRoots
    rw [sixVertexEvenSymmetricLift_projection (s + k + 1)
      hfixed.1.1.2.1]
    exact hfixed.1.1
  have hp (j : Fin n) : p j ∈ Set.Ioo 0 Real.pi := by
    exact sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + k) ⟨j.val, by dsimp [n] at j ⊢; omega⟩
  have heq :
      sixVertexCanonicalEvenBulkLogDisplacement hc s k -
          sixVertexCanonicalEvenRegularizedBulkLogDisplacement
            hc epsilon s k =
        ∑ j : Fin n,
          (sixVertexBetheLogRegularizationError c epsilon (q j) -
            sixVertexBetheLogRegularizationError c epsilon (p j)) := by
    unfold sixVertexCanonicalEvenBulkLogDisplacement
      sixVertexCanonicalEvenRegularizedBulkLogDisplacement
      sixVertexBetheLogRegularizationError
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [sixVertexBetheLogObservable_eq_logNormKernel hc (hq j),
      sixVertexBetheLogObservable_eq_logNormKernel hc (hp j)]
    ring
  rw [heq]
  simpa [q, p, n] using hk

end
end StatMech.FrontierD
