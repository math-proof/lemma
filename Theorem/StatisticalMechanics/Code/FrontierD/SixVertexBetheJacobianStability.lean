/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianSign
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianStability
open Finset Filter Topology Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheRootJacobian_toMatrix'_apply
    {N n : Nat} {c : Real} (hc : 2 < c)
    (p : Fin n → Real) (j k : Fin n) :
    LinearMap.toMatrix' (sixVertexBetheRootJacobian N n c p).toLinearMap j k =
      sixVertexBetheJacobianMatrix N n c p j k := by
  let R : (Fin n → Real) → (Fin n → Real) := fun q j =>
    sixVertexBetheResidual c N n q j
  have hR : HasFDerivAt R (sixVertexBetheRootJacobian N n c p) p := by
    exact (analyticAt_sixVertexBetheResidual_family N n (c, p) hc).comp
      (x := p) (f := fun q : Fin n → Real => (c, q))
      (analyticAt_const.prod analyticAt_id) |>.hasStrictFDerivAt.hasFDerivAt
  have hj : HasFDerivAt (fun q : Fin n → Real =>
      sixVertexBetheResidual c N n q j)
      ((ContinuousLinearMap.proj j).comp
        (sixVertexBetheRootJacobian N n c p)) p := by
    simpa [R] using (ContinuousLinearMap.proj j).hasFDerivAt.comp p hR
  have hdirect : HasFDerivAt (fun q : Fin n → Real =>
      sixVertexBetheResidual c N n q j)
      ((N : Real) • ContinuousLinearMap.proj j +
        ∑ l, (sixVertexThetaFDeriv c (p j) (p l)).comp
          ((ContinuousLinearMap.proj j).prod
            (ContinuousLinearMap.proj l))) p := by
    unfold sixVertexBetheResidual
    apply HasFDerivAt.sub_const
    apply HasFDerivAt.add
    · simpa using (hasFDerivAt_apply (𝕜 := Real) j p).const_mul (N : Real)
    · apply HasFDerivAt.fun_sum
      intro l _
      exact (hasFDerivAt_sixVertexTheta hc (p j) (p l)).comp p
        ((hasFDerivAt_apply (𝕜 := Real) j p).prodMk
          (hasFDerivAt_apply (𝕜 := Real) l p))
  have heq := hj.unique hdirect
  rw [LinearMap.toMatrix'_apply]
  change sixVertexBetheRootJacobian N n c p (Pi.single k 1) j = _
  have happly := congrArg
    (fun L : (Fin n → Real) →L[Real] Real => L (Pi.single k 1)) heq
  change sixVertexBetheRootJacobian N n c p (Pi.single k 1) j = _ at happly
  rw [happly]
  let P : Fin n → ((Fin n → Real) →L[Real] Real) :=
    fun i => ContinuousLinearMap.proj i
  change (((N : Real) • P j +
      ∑ l, (sixVertexThetaFDeriv c (p j) (p l)).comp
        ((P j).prod (P l))) (Pi.single k 1)) = _
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  rw [show (∑ l, (sixVertexThetaFDeriv c (p j) (p l)).comp
        ((P j).prod (P l))) (Pi.single k 1) =
      ∑ l, ((sixVertexThetaFDeriv c (p j) (p l)).comp
        ((P j).prod (P l))) (Pi.single k 1) by
    change (ContinuousLinearMap.apply Real Real (Pi.single k 1))
      (∑ l, (sixVertexThetaFDeriv c (p j) (p l)).comp
        ((P j).prod (P l))) = _
    rw [map_sum]
    rfl]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Finset.sum_apply,
    sixVertexThetaFDeriv, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  classical
  by_cases hjk : j = k
  · subst k
    rw [sixVertexBetheJacobianMatrix, if_pos rfl]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    simp_rw [P, ContinuousLinearMap.proj_apply, Pi.single_apply]
    rw [Finset.sum_add_distrib]
    have hzero : (∑ x ∈ Finset.univ.erase j,
        (if x = j then 1 else 0) *
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p j) /
            sixVertexThetaDerivativeDenominator c (p j) (p x))) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hxne := (Finset.mem_erase.mp hx).1
      simp [hxne]
    rw [hzero]
    simp
    ring
  · rw [sixVertexBetheJacobianMatrix, if_neg hjk]
    rw [Finset.sum_eq_single k]
    · simp [P, Pi.single_apply, hjk]
    · intro l _ hlk
      simp [P, Pi.single_apply, hlk, hjk]
    · exact fun hk => (hk (Finset.mem_univ k)).elim

end
end StatMech.FrontierD
