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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogBulk.Part3


namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

theorem tendsto_sixVertexCanonicalEvenRegularizedFullTaylorRemainder
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) (s : Nat) :
    Tendsto (fun k =>
      sixVertexCanonicalEvenRegularizedFullLogDisplacement hc epsilon s k -
        sixVertexCanonicalEvenRegularizedFullLinearTerm hc epsilon s k)
      atTop (nhds 0) := by
  let r := 2 * s
  let B := sixVertexCanonicalEvenOffsetUniformBound c hc s
  let L := (sixVertexRegularizedBetheLogNormSecondDerivativeNNReal
    c epsilon : Real)
  let majorant : Nat -> Real := fun k =>
    L * B ^ 2 / (sixVertexFourWidth r k : Real)
  have hB : 0 <= B := sixVertexCanonicalEvenOffsetUniformBound_nonneg hc s
  have hL : 0 <= L := NNReal.coe_nonneg _
  have hwidth : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp
    ((strictMono_nat_of_lt_succ (fun k => by unfold sixVertexFourWidth; omega)).tendsto_atTop)
  have hmajor : Tendsto majorant atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hwidth
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  apply squeeze_zero'
    (Eventually.of_forall fun k => norm_nonneg _) _ hmajor
  filter_upwards
    [eventually_abs_sixVertexCanonicalEvenChargeOffset_le hc s]
      with k hoff
  let N := sixVertexFourWidth r k
  let n := (s + k + 1) + (s + k + 1)
  let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  let p := sixVertexCanonicalEvenAlignedHalfRoots hc s k
  let off := sixVertexCanonicalEvenChargeOffset hc s k
  have hN : 0 < (N : Real) := by exact_mod_cast sixVertexFourWidth_pos r k
  have hdiff (i : Fin n) : q i - p i = off i / N := by
    dsimp only [off, sixVertexCanonicalEvenChargeOffset]
    change q i - p i = (N : Real) * (q i - p i) / N
    field_simp [hN.ne']
  have hterm (i : Fin n) :
      |(sixVertexRegularizedBetheLogKernel c epsilon (q i) -
          sixVertexRegularizedBetheLogKernel c epsilon (p i)) -
        sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          off i / N| <= L * B ^ 2 / N ^ 2 := by
    have ht := abs_sixVertexRegularizedBetheLogKernel_sub_linearization_le
      hc hepsilon (q i) (p i)
    have hoff' : |off i| <= B := by simpa [off] using hoff i
    have hpq : p i - q i = -(off i / N) := by
      rw [show p i - q i = -(q i - p i) by ring, hdiff]
    rw [show (sixVertexRegularizedBetheLogKernel c epsilon (q i) -
          sixVertexRegularizedBetheLogKernel c epsilon (p i)) -
        sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          off i / N =
      -(sixVertexRegularizedBetheLogKernel c epsilon (p i) -
          sixVertexRegularizedBetheLogKernel c epsilon (q i) -
        sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          (p i - q i)) by rw [hpq]; ring,
      abs_neg]
    calc
      _ <= L * |p i - q i| ^ 2 := ht
      _ <= L * (B / N) ^ 2 := by
        gcongr
        rw [abs_sub_comm, hdiff, abs_div, abs_of_pos hN]
        exact div_le_div_of_nonneg_right hoff' hN.le
      _ = L * B ^ 2 / N ^ 2 := by ring
  rw [Real.norm_eq_abs]
  unfold sixVertexCanonicalEvenRegularizedFullLogDisplacement
    sixVertexCanonicalEvenRegularizedFullLinearTerm
  dsimp [q, p, off, N, n, r]
  rw [<- Finset.sum_sub_distrib]
  calc
    |∑ i, ((sixVertexRegularizedBetheLogKernel c epsilon (q i) -
        sixVertexRegularizedBetheLogKernel c epsilon (p i)) -
      sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
        off i / N)| <=
      ∑ i, |(sixVertexRegularizedBetheLogKernel c epsilon (q i) -
          sixVertexRegularizedBetheLogKernel c epsilon (p i)) -
        sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          off i / N| := Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _i : Fin n, L * B ^ 2 / N ^ 2 :=
      Finset.sum_le_sum fun i _ => hterm i
    _ <= L * B ^ 2 / N := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hnN : (n : Real) <= N := by
        exact_mod_cast (by dsimp [n, N, r]; unfold sixVertexFourWidth; omega : n <= N)
      have hconst : 0 <= L * B ^ 2 := mul_nonneg hL (sq_nonneg B)
      rw [show (n : Real) * (L * B ^ 2 / N ^ 2) =
        (L * B ^ 2) * ((n : Real) / N) / N by ring]
      exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_right hconst ((div_le_one hN).2 hnN)) hN.le

theorem tendsto_sixVertexCanonicalEvenRegularizedBulkLogDisplacement
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) (s : Nat) :
    Tendsto (sixVertexCanonicalEvenRegularizedBulkLogDisplacement
      hc epsilon s) atTop
      (nhds ((2 * s : Real) / 2 *
        (∫ x in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x))) := by
  let target := (2 * s : Real) *
    (∫ x in -Real.pi..Real.pi,
      sixVertexRegularizedBetheLogNormDerivative c epsilon x *
        sixVertexContinuousOffsetFourier c hc x)
  have hfull : Tendsto
      (sixVertexCanonicalEvenRegularizedFullLogDisplacement hc epsilon s)
      atTop (nhds target) := by
    have h := (tendsto_sixVertexCanonicalEvenRegularizedFullTaylorRemainder
      hc hepsilon s).add
      (tendsto_sixVertexCanonicalEvenRegularizedFullLinearTerm hc hepsilon s)
    simpa [target] using h
  have htwice : Tendsto
      (fun k => 2 * sixVertexCanonicalEvenRegularizedBulkLogDisplacement
        hc epsilon s k) atTop (nhds target) :=
    hfull.congr' (eventually_full_regularizedLogDisplacement_eq_two_positive
      hc epsilon s)
  have hhalf := htwice.const_mul (1 / 2 : Real)
  have htarget :
      (1 / 2 : Real) * target = (2 * s : Real) / 2 *
        (∫ x in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x) := by
    dsimp [target]
    ring
  rw [htarget] at hhalf
  simpa using hhalf

end
end StatMech.FrontierD
