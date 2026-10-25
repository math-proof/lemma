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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogBulk.Part2


namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

theorem tendsto_sixVertexCanonicalEvenRegularizedFullLinearTerm
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) (s : Nat) :
    Tendsto (sixVertexCanonicalEvenRegularizedFullLinearTerm hc epsilon s)
      atTop (nhds ((2 * s : Real) *
        (∫ x in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x))) := by
  let r := 2 * s
  let lower := sixVertexCanonicalFixedEvenDensityFloor hc s
  let U := sixVertexRegularizedBetheLogNormDerivativeBound c epsilon
  let G := sixVertexContinuousOffsetFourierBound c
  let Lu := sixVertexRegularizedBetheLogNormSecondDerivativeNNReal c epsilon
  let D := sixVertexContinuousOffsetFourierLipschitzNNReal c
  let Q := sixVertexLogOffsetQuotientLipschitzNNReal c lower U G Lu D
  let F := U * G / lower
  let integral := ∫ x in -Real.pi..Real.pi,
    sixVertexRegularizedBetheLogNormDerivative c epsilon x *
      sixVertexContinuousOffsetFourier c hc x
  let empirical : Nat -> Real := fun k =>
    let N := sixVertexFourWidth r k
    let n := (s + k + 1) + (s + k + 1)
    let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
    (∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
      sixVertexContinuousOffsetFourier c hc (q i) /
        sixVertexFiniteRootDensity c N n q (q i)) / N
  have hlower : 0 < lower := sixVertexCanonicalFixedEvenDensityFloor_pos hc s
  have hU : 0 <= U := by
    dsimp [U, sixVertexRegularizedBetheLogNormDerivativeBound]
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    have hd : 0 < c ^ 2 - 2 := by nlinarith
    positivity
  have hG : 0 <= G := by
    dsimp [G, sixVertexContinuousOffsetFourierBound]
    positivity
  have hwidth : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp
    ((strictMono_nat_of_lt_succ (fun k => by unfold sixVertexFourWidth; omega)).tendsto_atTop)
  have hquad : Tendsto empirical atTop (nhds integral) := by
    let err : Nat -> Real := fun k =>
      (Q : Real) * sixVertexFiniteRootDensityUniformBound c *
          ((2 * (r : Real) + 1) /
            ((sixVertexFourWidth r k : Real) * lower)) * (2 * Real.pi) +
        (2 * (r : Real) / sixVertexFourWidth r k) * F +
        2 * F / sixVertexFourWidth r k +
        sixVertexFiniteRootDensityUniformBound c * F *
          ((2 * (r : Real) + 1) /
            ((sixVertexFourWidth r k : Real) * lower))
    have herr : Tendsto err atTop (nhds 0) := by
      have hzero : Tendsto (fun k : Nat =>
          (1 : Real) / (sixVertexFourWidth r k : Real)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hwidth
      convert hzero.const_mul
        ((Q : Real) * sixVertexFiniteRootDensityUniformBound c *
            ((2 * (r : Real) + 1) / lower) * (2 * Real.pi) +
          2 * (r : Real) * F + 2 * F +
          sixVertexFiniteRootDensityUniformBound c * F *
            ((2 * (r : Real) + 1) / lower)) using 1
      · funext k
        dsimp [err]
        field_simp [hlower.ne']
      · ring
    rw [Metric.tendsto_atTop] at herr
    apply Metric.tendsto_atTop.2
    intro delta hdelta
    obtain ⟨Kerr, hKerr⟩ := herr delta hdelta
    obtain ⟨Kwit, hKwit⟩ :=
      (eventually_atTop.1
        (eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness
          hc s))
    refine ⟨max Kerr Kwit, ?_⟩
    intro k hkmax
    have hkerr : Kerr <= k := le_trans (le_max_left _ _) hkmax
    have hk := hKwit k (le_trans (le_max_right _ _) hkmax)
    have hN : 0 < sixVertexFourWidth r k := sixVertexFourWidth_pos r k
    let n := (s + k + 1) + (s + k + 1)
    let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
    have hcharge : sixVertexFourWidth r k = 2 * n + 2 * r := by
      dsimp [n, r]
      unfold sixVertexFourWidth
      omega
    have hqLip := lipschitzWith_mul_div_sixVertexFiniteRootDensity hc hN
      (by dsimp [n, r]; unfold sixVertexFourWidth; omega) q hlower hU hG
      hk.2
      (lipschitzWith_sixVertexRegularizedBetheLogNormDerivative hc hepsilon)
      (fun x => abs_sixVertexRegularizedBetheLogNormDerivative_le hc hepsilon)
      (lipschitzWith_sixVertexContinuousOffsetFourier hc)
      (abs_sixVertexContinuousOffsetFourier_le hc)
    have hbound (x : Real) :
        |sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x /
              sixVertexFiniteRootDensity c (sixVertexFourWidth r k) n q x| <= F := by
      rw [abs_div, abs_mul, abs_of_pos (hlower.trans_le (hk.2 x))]
      have hprod :
          |sixVertexRegularizedBetheLogNormDerivative c epsilon x| *
              |sixVertexContinuousOffsetFourier c hc x| <= U * G := mul_le_mul
        (abs_sixVertexRegularizedBetheLogNormDerivative_le
          (x := x) hc hepsilon)
        (abs_sixVertexContinuousOffsetFourier_le hc x)
        (abs_nonneg _) hU
      calc
        _ <= U * G /
            sixVertexFiniteRootDensity c (sixVertexFourWidth r k) n q x :=
          div_le_div_of_nonneg_right hprod
            (hlower.trans_le (hk.2 x)).le
        _ <= U * G / lower :=
          div_le_div_of_nonneg_left (mul_nonneg hU hG) hlower (hk.2 x)
    have h := abs_empiricalLipschitz_sub_finiteDensityIntegral_fixedCharge_nonperiodic
      hc hN hcharge hk.1.1 hk.1.2.1 hlower hk.2 hqLip.continuous hqLip hbound
    have hintegral :
        (∫ y in -Real.pi..Real.pi,
          (sixVertexRegularizedBetheLogNormDerivative c epsilon y *
            sixVertexContinuousOffsetFourier c hc y /
              sixVertexFiniteRootDensity c (sixVertexFourWidth r k) n q y) *
            sixVertexFiniteRootDensity c (sixVertexFourWidth r k) n q y) =
          integral := by
      dsimp only [integral]
      apply intervalIntegral.integral_congr
      intro y _
      have hry : sixVertexFiniteRootDensity c (sixVertexFourWidth r k) n q y ≠ 0 :=
        (hlower.trans_le (hk.2 y)).ne'
      exact div_mul_cancel₀ _ hry
    change |empirical k -
      (∫ y in -Real.pi..Real.pi,
        (sixVertexRegularizedBetheLogNormDerivative c epsilon y *
          sixVertexContinuousOffsetFourier c hc y /
            sixVertexFiniteRootDensity c (sixVertexFourWidth r k) n q y) *
          sixVertexFiniteRootDensity c (sixVertexFourWidth r k) n q y)| <=
        err k at h
    rw [hintegral] at h
    have herrk := hKerr k hkerr
    rw [Real.dist_eq, sub_zero] at herrk
    exact (h.trans (le_abs_self (err k))).trans_lt herrk
  have hreplace : Tendsto
      (fun k => sixVertexCanonicalEvenRegularizedFullLinearTerm hc epsilon s k -
        (r : Real) * empirical k) atTop (nhds 0) := by
    apply Metric.tendsto_atTop.2
    intro delta hdelta
    have hUpos : 0 < U := by
      dsimp [U, sixVertexRegularizedBetheLogNormDerivativeBound]
      have ha : 0 < c ^ 2 - 1 := by nlinarith
      have hd : 0 < c ^ 2 - 2 := by nlinarith
      positivity
    have hcoef : 0 < U / lower := div_pos hUpos hlower
    let eta := delta / (U / lower)
    have heta : 0 < eta := div_pos hdelta hcoef
    obtain ⟨Kwit, hKwit⟩ := eventually_atTop.1
      (eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s)
    obtain ⟨Koff, hKoff⟩ := eventually_atTop.1
      (eventually_uniform_sixVertexCanonicalEvenDensityOffset_fourier hc s heta)
    refine ⟨max Kwit Koff, ?_⟩
    intro k hkmax
    have hk := hKwit k (le_trans (le_max_left _ _) hkmax)
    have hoff := hKoff k (le_trans (le_max_right _ _) hkmax)
    let N := sixVertexFourWidth r k
    let n := (s + k + 1) + (s + k + 1)
    let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
    let rho := sixVertexFiniteRootDensity c N n q
    have hN : 0 < (N : Real) := by exact_mod_cast sixVertexFourWidth_pos r k
    have hterm (i : Fin n) :
        |sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          (sixVertexCanonicalEvenChargeOffset hc s k i -
            (r : Real) * sixVertexContinuousOffsetFourier c hc (q i) /
              rho (q i)) / N| < delta / N := by
      have hrho : 0 < rho (q i) := hlower.trans_le (hk.2 _)
      have hoff' :
          |rho (q i) * sixVertexCanonicalEvenChargeOffset hc s k i -
            (r : Real) * sixVertexContinuousOffsetFourier c hc (q i)| <
              eta := by
        simpa [rho, q, n, N, r] using hoff i
      rw [show sixVertexCanonicalEvenChargeOffset hc s k i -
          (r : Real) * sixVertexContinuousOffsetFourier c hc (q i) /
            rho (q i) =
        (rho (q i) * sixVertexCanonicalEvenChargeOffset hc s k i -
          (r : Real) * sixVertexContinuousOffsetFourier c hc (q i)) /
            rho (q i) by field_simp [hrho.ne']]
      rw [abs_div, abs_mul, abs_div, abs_of_pos hN, abs_of_pos hrho]
      calc
        _ <= U * |rho (q i) * sixVertexCanonicalEvenChargeOffset hc s k i -
              (r : Real) * sixVertexContinuousOffsetFourier c hc (q i)| /
            rho (q i) / N := by
          apply div_le_div_of_nonneg_right _ hN.le
          have hder :
              |sixVertexRegularizedBetheLogNormDerivative c epsilon (q i)| <= U := by
            simpa [U] using
              (abs_sixVertexRegularizedBetheLogNormDerivative_le
                (x := q i) hc hepsilon)
          calc
            _ <= U *
                (|rho (q i) * sixVertexCanonicalEvenChargeOffset hc s k i -
                  (r : Real) * sixVertexContinuousOffsetFourier c hc (q i)| /
                    rho (q i)) :=
              mul_le_mul_of_nonneg_right hder
                (div_nonneg (abs_nonneg _) hrho.le)
            _ = _ := by ring
        _ < U * eta / rho (q i) / N := by
          gcongr
        _ <= U * eta / lower / N := by
          have hnum : 0 <= U * eta := mul_nonneg hU heta.le
          exact div_le_div_of_nonneg_right
            (div_le_div_of_nonneg_left hnum hlower (hk.2 _)) hN.le
        _ = delta / N := by dsimp [eta]; field_simp [hcoef.ne', hlower.ne']
    unfold sixVertexCanonicalEvenRegularizedFullLinearTerm
    dsimp [empirical, N, n, q, r]
    rw [Real.dist_eq, sub_zero]
    have hrearrange :
        (∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
            sixVertexCanonicalEvenChargeOffset hc s k i / N) -
          (r : Real) *
            ((∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
              sixVertexContinuousOffsetFourier c hc (q i) / rho (q i)) / N) =
        ∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          (sixVertexCanonicalEvenChargeOffset hc s k i -
            (r : Real) * sixVertexContinuousOffsetFourier c hc (q i) /
              rho (q i)) / N := by
      calc
        _ = ∑ i,
            (sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
                sixVertexCanonicalEvenChargeOffset hc s k i / N -
              (r : Real) *
                (sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
                  sixVertexContinuousOffsetFourier c hc (q i) / rho (q i)) /
                    N) := by
          rw [Finset.sum_sub_distrib]
          congr 1
          calc
            (r : Real) *
                ((∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
                  sixVertexContinuousOffsetFourier c hc (q i) / rho (q i)) / N) =
              (∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
                sixVertexContinuousOffsetFourier c hc (q i) / rho (q i)) *
                  ((r : Real) / N) := by ring
            _ = ∑ i, (sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
                sixVertexContinuousOffsetFourier c hc (q i) / rho (q i)) *
                  ((r : Real) / N) := by rw [Finset.sum_mul]
            _ = _ := by
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    rw [hrearrange]
    calc
      |∑ i, sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          (sixVertexCanonicalEvenChargeOffset hc s k i -
            (r : Real) * sixVertexContinuousOffsetFourier c hc (q i) /
              rho (q i)) / N| <=
        ∑ i, |sixVertexRegularizedBetheLogNormDerivative c epsilon (q i) *
          (sixVertexCanonicalEvenChargeOffset hc s k i -
            (r : Real) * sixVertexContinuousOffsetFourier c hc (q i) /
              rho (q i)) / N| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _i : Fin n, delta / N := Finset.sum_lt_sum_of_nonempty
        Finset.univ_nonempty (fun i _ => hterm i)
      _ <= delta := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        have hnN : (n : Real) <= N := by
          exact_mod_cast (by dsimp [n, N, r]; unfold sixVertexFourWidth; omega : n <= N)
        calc
          (n : Real) * (delta / N) = ((n : Real) / N) * delta := by ring
          _ <= 1 * delta :=
            mul_le_mul_of_nonneg_right ((div_le_one hN).2 hnN) hdelta.le
          _ = delta := one_mul _
  have hmain := hreplace.add ((hquad.const_mul (r : Real)).sub_const
    ((r : Real) * integral))
  simpa [integral, empirical, r] using
    (hreplace.add (hquad.const_mul (r : Real)))

end
end StatMech.FrontierD
