/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisCore.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisBridge.Part2


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem log_sixVertexCanonicalOddWallisProductRatio_sq
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Real.log (sixVertexCanonicalOddWallisProductRatio hc s k ^ 2) =
      sixVertexCanonicalOddSmoothWallisLog hc s k -
        2 * (
          let N := sixVertexFourWidth (2 * s + 1) k
          let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
          let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
          ∑ j : Fin (s + k + 1),
            (Real.log (sixVertexBetheCountingFunction c N n p
                (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) -
              Real.log (((j : Real) + 1) / N))) := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  let A := sixVertexCanonicalOddActualHalfProduct hc s k
  let W := sixVertexOddWallisHalfProduct (s + k + 1)
  have hA : 0 < A := sixVertexCanonicalOddActualHalfProduct_pos hc s k
  have hW : 0 < W := by
    dsimp [W, sixVertexOddWallisHalfProduct]
    exact Finset.prod_pos fun j hj => div_pos (by positivity) (by positivity)
  have hterm (j : Fin (s + k + 1)) :
      0 < ‖sixVertexBetheM c (sixVertexBethePhase
          (sixVertexCanonicalOddMidpointHalfRoot hc s k j))‖ /
        ‖sixVertexBetheM c (sixVertexBethePhase
          (sixVertexCanonicalOddLeftHalfRoot hc s k j))‖ :=
    div_pos (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _))
      (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _))
  have hlogA : Real.log A =
      ∑ j : Fin (s + k + 1),
        (sixVertexBetheLogObservable c
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
          sixVertexBetheLogObservable c
            (sixVertexCanonicalOddLeftHalfRoot hc s k j)) := by
    dsimp [A, sixVertexCanonicalOddActualHalfProduct,
      sixVertexBetheLogObservable]
    rw [Real.log_prod (fun j hj => (hterm j).ne')]
    simp_rw [Real.log_div
      (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _)).ne'
      (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _)).ne']
  have hlogW : Real.log W =
      ∑ j : Fin (s + k + 1),
        (Real.log (sixVertexBetheCountingFunction c N n p
            (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
          Real.log (((j : Real) + 1) / N)) := by
    have hN : 0 < (N : Real) := by
      exact_mod_cast sixVertexFourWidth_pos (2 * s + 1) k
    have hNne : (sixVertexFourWidth (2 * s + 1) k : Real) ≠ 0 := by
      exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'
    have href :
        (∑ j : Fin (s + k + 1),
          (Real.log (sixVertexBetheCountingFunction c N n p
              (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
            Real.log (((j : Real) + 1) / N))) =
          sixVertexOddWallisReferenceLogSum (s + k + 1) := by
      calc
        _ = ∑ j : Fin (s + k + 1),
            Real.log (((2 * j.val + 1 : Nat) : Real) /
              (2 * j.val + 2)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [sixVertexCanonicalOddLeftHalfRoot_countingFunction hc s k j]
          dsimp [N]
          rw [← Real.log_div]
          · congr 1
            field_simp [hN.ne']
            push_cast
            simp [hNne, mul_assoc]
            ring
          · positivity
          · positivity
        _ = ∑ j ∈ Finset.range (s + k + 1),
            Real.log (((2 * j + 1 : Nat) : Real) / (2 * j + 2)) := by
          simpa using (Fin.sum_univ_eq_sum_range (fun j : Nat =>
            Real.log (((2 * j + 1 : Nat) : Real) / (2 * j + 2)))
              (s + k + 1))
        _ = _ := rfl
    exact (sixVertexOddWallisReferenceLogSum_eq_log _).symm.trans href.symm
  unfold sixVertexCanonicalOddWallisProductRatio
  rw [Real.log_pow, Real.log_div hA.ne' hW.ne', hlogA, hlogW]
  dsimp [sixVertexCanonicalOddSmoothWallisLog, N, n, p]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [div_eq_mul_inv, add_mul, one_mul, mul_comm, add_comm]
  ring_nf

theorem sixVertexCanonicalOddGeneralizedWallisComparison_of_smooth
    {c : Real} (hc : 2 < c) (s : Nat)
    (hsmooth : SixVertexCanonicalOddSmoothWallisLimit hc s) :
    SixVertexCanonicalOddGeneralizedWallisComparison hc s := by
  let E : Nat → Real := fun k =>
    let N := sixVertexFourWidth (2 * s + 1) k
    let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
    let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
    ∑ j : Fin (s + k + 1),
      (Real.log (sixVertexBetheCountingFunction c N n p
          (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) -
        Real.log (((j : Real) + 1) / N))
  let L := Real.cosh (sixVertexAntiferroelectricLambda c) /
    (4 * c ^ 2 * sixVertexFourierPhysicalDensity c hc 0)
  have hE : Tendsto E atTop (nhds 0) :=
    tendsto_sum_log_sixVertexCanonicalOddMidpointCounting_sub_reference hc s
  have hlog : Tendsto (fun k => Real.log
      (sixVertexCanonicalOddWallisProductRatio hc s k ^ 2)) atTop
      (nhds (Real.log L)) := by
    have h := hsmooth.sub (hE.const_mul 2)
    simpa [E, L, log_sixVertexCanonicalOddWallisProductRatio_sq hc s] using h
  have hexp : Tendsto (fun k => Real.exp (Real.log
      (sixVertexCanonicalOddWallisProductRatio hc s k ^ 2))) atTop
      (nhds (Real.exp (Real.log L))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hpos : 0 < L := by
    dsimp [L]
    exact div_pos (Real.cosh_pos _)
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
        (sixVertexFourierPhysicalDensity_pos hc 0))
  unfold SixVertexCanonicalOddGeneralizedWallisComparison
  have hexp' : Tendsto (fun k =>
      sixVertexCanonicalOddWallisProductRatio hc s k ^ 2) atTop
      (nhds L) := by
    rw [← Real.exp_log hpos]
    apply hexp.congr'
    filter_upwards [] with k
    rw [Real.exp_log]
    exact pow_pos (div_pos
      (sixVertexCanonicalOddActualHalfProduct_pos hc s k)
      (by
        unfold sixVertexOddWallisHalfProduct
        exact Finset.prod_pos fun j hj => div_pos (by positivity) (by positivity))) 2
  exact hexp'

end
end StatMech.FrontierD
