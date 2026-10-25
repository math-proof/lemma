/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalParameter.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

theorem hasDerivAt_triangularIsingSymbol_along_ray
    (J beta p q : Real) :
    HasDerivAt
      (fun b => triangularIsingSymbol b b (b * J) p q)
      (triangularIsingRaySymbolDeriv J beta p q) beta := by
  have hlin : HasDerivAt (fun b : Real => 2 * b) 2 beta := by
    convert (hasDerivAt_id beta).const_mul 2 using 1 <;> ring
  have hlinJ : HasDerivAt (fun b : Real => 2 * b * J) (2 * J) beta := by
    convert ((hasDerivAt_id beta).const_mul 2).mul_const J using 1 <;> ring
  have hC := (Real.hasDerivAt_cosh (2 * beta)).comp beta hlin
  have hS := (Real.hasDerivAt_sinh (2 * beta)).comp beta hlin
  have hCJ := (Real.hasDerivAt_cosh (2 * beta * J)).comp beta hlinJ
  have hSJ := (Real.hasDerivAt_sinh (2 * beta * J)).comp beta hlinJ
  have h := ((hC.pow 2).mul hCJ).add ((hS.pow 2).mul hSJ) |>.sub
    ((hS.mul_const (Real.cos p + Real.cos q)).add
      (hSJ.mul_const (Real.cos (p + q))))
  convert h using 1
  · ext b
    change triangularIsingSymbol b b (b * J) p q =
      Real.cosh (2 * b) ^ 2 * Real.cosh (2 * b * J) +
        Real.sinh (2 * b) ^ 2 * Real.sinh (2 * b * J) -
        (Real.sinh (2 * b) * (Real.cos p + Real.cos q) +
          Real.sinh (2 * b * J) * Real.cos (p + q))
    unfold triangularIsingSymbol
    ring
  · unfold triangularIsingRaySymbolDeriv
    simp only [Function.comp_apply, Pi.pow_apply, Nat.reduceSub, pow_one]
    ring

theorem triangularIsingRaySymbolDeriv_sub_zero
    (J beta p q : Real) :
    triangularIsingRaySymbolDeriv J beta p q -
        triangularIsingRaySymbolDeriv J beta 0 0 =
      2 * Real.cosh (2 * beta) *
          ((1 - Real.cos p) + (1 - Real.cos q)) +
        2 * J * Real.cosh (2 * beta * J) *
          (1 - Real.cos (p + q)) := by
  simp [triangularIsingRaySymbolDeriv]
  ring

theorem triangularIsingRaySymbolDeriv_zero_at_root
    {beta J : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    triangularIsingRaySymbolDeriv J beta 0 0 = 0 := by
  let P := triangularIsingCriticalPolynomialAlong J
  let H := triangularIsingZeroModePrefactorAlong J
  have hP : HasDerivAt P (deriv P beta) beta :=
    (differentiableAt_triangularIsingCriticalPolynomialAlong J beta).hasDerivAt
  have hH : HasDerivAt H (deriv H beta) beta := by
    exact (by unfold H triangularIsingZeroModePrefactorAlong; fun_prop :
      DifferentiableAt Real H beta).hasDerivAt
  have hPzero : P beta = 0 :=
    (triangularIsingCriticalPolynomial_zero_iff_rate_eq_one hbeta).2 hroot
  have hright : HasDerivAt (fun b => P b ^ 2 * H b) 0 beta := by
    convert (hP.pow 2).mul hH using 1
    simp [hPzero]
  have heq : (fun b => triangularIsingSymbol b b (b * J) 0 0) =
      fun b => P b ^ 2 * H b := by
    funext b
    exact triangularIsing_zeroMode_eq_polynomialAlong_sq_mul J b
  have hright' : HasDerivAt
      (fun b => triangularIsingSymbol b b (b * J) 0 0) 0 beta := by
    rw [heq]
    exact hright
  exact (hasDerivAt_triangularIsingSymbol_along_ray J beta 0 0).unique hright'

theorem differentiable_triangularIsingRaySymbolDeriv (J p q : Real) :
    Differentiable Real (fun b => triangularIsingRaySymbolDeriv J b p q) := by
  unfold triangularIsingRaySymbolDeriv
  fun_prop


set_option maxHeartbeats 800000 in

theorem exists_triangularIsingCriticalRay_local_bounds
    {beta J : Real} (hbeta : 0 < beta) (hJ : -1 < J)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    ∃ U : Set Real, U ∈ nhds beta ∧ IsOpen U ∧
      ∃ m K : Real, 0 < m ∧ 0 < K ∧ ∀ b ∈ U, ∀ p q : Real,
        m * ((b - beta) ^ 2 +
            ((1 - Real.cos p) + (1 - Real.cos q))) <=
          triangularIsingSymbol b b (b * J) p q ∧
        |triangularIsingRaySymbolDeriv J b p q| <=
          K * (2 * |b - beta| +
            ((1 - Real.cos p) + (1 - Real.cos q))) := by
  let P := triangularIsingCriticalPolynomialAlong J
  let H := triangularIsingZeroModePrefactorAlong J
  let D0 : Real -> Real := fun b => triangularIsingRaySymbolDeriv J b 0 0
  let g : Real -> Real := fun b =>
    if 0 <= J then Real.sinh (2 * b)
    else Real.sinh (2 * b) + 2 * Real.sinh (2 * b * J)
  have hP : HasDerivAt P (deriv P beta) beta :=
    (differentiableAt_triangularIsingCriticalPolynomialAlong J beta).hasDerivAt
  have hPne : deriv P beta ≠ 0 := by
    exact (deriv_triangularIsingCriticalPolynomialAlong_neg_at_root
      hbeta (by linarith) hroot).ne
  have hPzero : P beta = 0 :=
    (triangularIsingCriticalPolynomial_zero_iff_rate_eq_one hbeta).2 hroot
  obtain ⟨CP, hCP, hPbig⟩ := (hP.isTheta_sub hPne).isBigO_symm.exists_pos
  have hPbound : ∀ᶠ b in nhds beta, |b - beta| <= CP * |P b| := by
    have ht : Tendsto (fun b : Real => (b, beta)) (nhds beta)
        (nhds beta ×ˢ pure beta) := tendsto_id.prodMk tendsto_const_pure
    filter_upwards [ht.eventually hPbig.bound] with b hb
    simpa only [Real.norm_eq_abs, hPzero, sub_zero] using hb
  have hHbeta : 0 < H beta := by
    unfold H triangularIsingZeroModePrefactorAlong
    positivity
  have hHbound : ∀ᶠ b in nhds beta, H beta / 2 <= H b := by
    exact (continuous_triangularIsingZeroModePrefactorAlong J).continuousAt
      |>.eventually (eventually_ge_nhds (by linarith : H beta / 2 < H beta))
  have hpos : ∀ᶠ b in nhds beta, 0 < b := eventually_gt_nhds hbeta
  have hgbeta : 0 < g beta := by
    by_cases hJnonneg : 0 <= J
    · simp only [g, if_pos hJnonneg]
      exact Real.sinh_pos_iff.mpr (by linarith)
    · simp only [g, if_neg hJnonneg]
      have hs : 0 < Real.sinh (2 * beta) :=
        Real.sinh_pos_iff.mpr (by linarith)
      have hrate := hroot
      rw [triangularIsingCriticalRate] at hrate
      have harg : 2 * (beta * J) = 2 * beta * J := by ring
      rw [harg] at hrate
      have hprod : 0 < Real.sinh (2 * beta) *
          (Real.sinh (2 * beta) + 2 * Real.sinh (2 * beta * J)) := by
        nlinarith
      rcases mul_pos_iff.mp hprod with hpos | hneg
      · exact hpos.2
      · exact (lt_asymm hs hneg.1).elim
  have hgbound : ∀ᶠ b in nhds beta, g beta / 2 <= g b := by
    have hgcont : Continuous g := by
      unfold g
      split <;> fun_prop
    exact hgcont.continuousAt.eventually
      (eventually_ge_nhds (by linarith : g beta / 2 < g beta))
  have hDdiff : DifferentiableAt Real D0 beta := by
    exact differentiable_triangularIsingRaySymbolDeriv J 0 0 beta
  obtain ⟨CD, hCD, hDbig⟩ := hDdiff.isBigO_sub.exists_pos
  have hDzero : D0 beta = 0 :=
    triangularIsingRaySymbolDeriv_zero_at_root hbeta hroot
  have hDbound : ∀ᶠ b in nhds beta, |D0 b| <= CD * |b - beta| := by
    filter_upwards [hDbig.bound] with b hb
    simpa only [Real.norm_eq_abs, hDzero, sub_zero] using hb
  let Cmom : Real :=
    2 * (|Real.cosh (2 * beta)| + 1) +
      4 * |J| * (|Real.cosh (2 * beta * J)| + 1)
  have hCmom : 0 < Cmom := by
    unfold Cmom
    positivity
  have hcosh : ∀ᶠ b in nhds beta,
      |Real.cosh (2 * b)| < |Real.cosh (2 * beta)| + 1 := by
    have hc : Continuous (fun b : Real => |Real.cosh (2 * b)|) := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by linarith)
  have hcoshJ : ∀ᶠ b in nhds beta,
      |Real.cosh (2 * b * J)| < |Real.cosh (2 * beta * J)| + 1 := by
    have hc : Continuous (fun b : Real => |Real.cosh (2 * b * J)|) := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by linarith)
  let a : Real := H beta / (2 * CP ^ 2)
  let c : Real := g beta / 2
  let m : Real := min a c
  let K : Real := max (CD + 1) Cmom
  have ha : 0 < a := by unfold a; positivity
  have hc : 0 < c := by
    unfold c
    positivity
  have hm : 0 < m := by simp only [m, lt_min_iff]; exact ⟨ha, hc⟩
  have hK : 0 < K := lt_of_lt_of_le hCmom (le_max_right _ _)
  let S : Set Real := {b | 0 < b ∧
      |b - beta| <= CP * |P b| ∧
      H beta / 2 <= H b ∧
      c <= g b ∧
      |D0 b| <= CD * |b - beta| ∧
      |Real.cosh (2 * b)| <= |Real.cosh (2 * beta)| + 1 ∧
      |Real.cosh (2 * b * J)| <= |Real.cosh (2 * beta * J)| + 1}
  have hS : S ∈ nhds beta := by
    filter_upwards [hpos, hPbound, hHbound, hgbound, hDbound,
      hcosh, hcoshJ] with b hb hp hH hs hD hC hCJ
    exact ⟨hb, hp, hH, hs, hD, hC.le, hCJ.le⟩
  obtain ⟨U, hUS, hUopen, hbetaU⟩ := mem_nhds_iff.mp hS
  have hU : U ∈ nhds beta := hUopen.mem_nhds hbetaU
  refine ⟨U, hU, hUopen, m, K, hm, hK, ?_⟩
  intro b hb p q
  have hbS := hUS hb
  let A : Real := (1 - Real.cos p) + (1 - Real.cos q)
  let B : Real := 1 - Real.cos (p + q)
  have hA : 0 <= A := by
    unfold A
    nlinarith [Real.cos_le_one p, Real.cos_le_one q]
  have hB : 0 <= B := by unfold B; linarith [Real.cos_le_one (p + q)]
  have hBA : B <= 2 * A := one_sub_cos_add_le_two_sum p q
  have hPsq : (b - beta) ^ 2 <= CP ^ 2 * P b ^ 2 := by
    have hsquare := sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hCP.le (abs_nonneg _)) |>.2 hbS.2.1
    nlinarith [hsquare, sq_abs (b - beta), sq_abs (P b)]
  have hzero : a * (b - beta) ^ 2 <=
      triangularIsingSymbol b b (b * J) 0 0 := by
    rw [triangularIsing_zeroMode_eq_polynomialAlong_sq_mul]
    have hH : H beta / 2 <= H b := hbS.2.2.1
    have hCP0 : CP ^ 2 > 0 := sq_pos_of_pos hCP
    unfold a
    calc
      H beta / (2 * CP ^ 2) * (b - beta) ^ 2 <=
          H beta / (2 * CP ^ 2) * (CP ^ 2 * P b ^ 2) := by
            gcongr
      _ = H beta / 2 * P b ^ 2 := by
            field_simp [hCP.ne']
      _ <= P b ^ 2 * H b := by
            nlinarith [sq_nonneg (P b)]
  have hmA : m * ((b - beta) ^ 2 + A) <=
      a * (b - beta) ^ 2 + c * A := by
    have hma : m <= a := min_le_left _ _
    have hmc : m <= c := min_le_right _ _
    nlinarith [sq_nonneg (b - beta)]
  have hexcess := triangularIsingSymbol_sub_zero b (b * J) p q
  change triangularIsingSymbol b b (b * J) p q -
      triangularIsingSymbol b b (b * J) 0 0 =
        Real.sinh (2 * b) * A + Real.sinh (2 * (b * J)) * B at hexcess
  have hmomentumLower : c * A <=
      Real.sinh (2 * b) * A + Real.sinh (2 * (b * J)) * B := by
    have hg : c <= g b := hbS.2.2.2.1
    by_cases hJnonneg : 0 <= J
    · have hgeq : g b = Real.sinh (2 * b) := by
        simp only [g, if_pos hJnonneg]
      have hr : 0 <= Real.sinh (2 * (b * J)) :=
        Real.sinh_nonneg_iff.mpr (by
          exact mul_nonneg (by norm_num)
            (mul_nonneg hbS.1.le hJnonneg))
      have hsA := mul_le_mul_of_nonneg_right (hgeq ▸ hg) hA
      nlinarith [mul_nonneg hr hB]
    · have hJneg : J < 0 := lt_of_not_ge hJnonneg
      have hr : Real.sinh (2 * (b * J)) < 0 :=
        Real.sinh_neg_iff.mpr (by
          have := mul_neg_of_pos_of_neg hbS.1 hJneg
          linarith)
      have hgeq : g b = Real.sinh (2 * b) +
          2 * Real.sinh (2 * b * J) := by
        simp only [g, if_neg hJnonneg]
      have hrB : 2 * Real.sinh (2 * (b * J)) * A <=
          Real.sinh (2 * (b * J)) * B := by
        have := mul_le_mul_of_nonpos_left hBA hr.le
        nlinarith
      have hgA := mul_le_mul_of_nonneg_right hg hA
      rw [hgeq] at hgA
      have harg : 2 * (b * J) = 2 * b * J := by ring
      rw [harg] at hrB ⊢
      linarith [hgA]
  have hlower : a * (b - beta) ^ 2 + c * A <=
      triangularIsingSymbol b b (b * J) p q := by
    linarith [hzero, hexcess, hmomentumLower]
  refine ⟨hmA.trans hlower, ?_⟩
  have hdiff := triangularIsingRaySymbolDeriv_sub_zero J b p q
  have hmomentum :
      |triangularIsingRaySymbolDeriv J b p q - D0 b| <= Cmom * A := by
    rw [hdiff]
    have hterm1 : |2 * Real.cosh (2 * b) * A| <=
        (2 * (|Real.cosh (2 * beta)| + 1)) * A := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2),
        abs_of_nonneg hA]
      gcongr
      exact hbS.2.2.2.2.2.1
    have hterm2 : |2 * J * Real.cosh (2 * b * J) * B| <=
        (4 * |J| * (|Real.cosh (2 * beta * J)| + 1)) * A := by
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : Real) <= 2), abs_of_nonneg hB]
      have hcJ := hbS.2.2.2.2.2.2
      calc
        2 * |J| * |Real.cosh (2 * b * J)| * B <=
            2 * |J| * (|Real.cosh (2 * beta * J)| + 1) * B := by gcongr
        _ <= 2 * |J| * (|Real.cosh (2 * beta * J)| + 1) * (2 * A) := by gcongr
        _ = _ := by ring
    calc
      |_ + _| <= |2 * Real.cosh (2 * b) * A| +
          |2 * J * Real.cosh (2 * b * J) * B| := abs_add_le _ _
      _ <= Cmom * A := by unfold Cmom; linarith
  have hD0 : |D0 b| <= (CD + 1) * |b - beta| := by
    have := hbS.2.2.2.2.1
    nlinarith [abs_nonneg (b - beta)]
  have htotal : |triangularIsingRaySymbolDeriv J b p q| <=
      (CD + 1) * |b - beta| + Cmom * A := by
    calc
      |triangularIsingRaySymbolDeriv J b p q| =
          |(triangularIsingRaySymbolDeriv J b p q - D0 b) + D0 b| := by ring_nf
      _ <= |triangularIsingRaySymbolDeriv J b p q - D0 b| + |D0 b| :=
        abs_add_le _ _
      _ <= _ := by linarith
  have hCDK : CD + 1 <= K := le_max_left _ _
  have hCK : Cmom <= K := le_max_right _ _
  have hK0 : 0 <= K := hK.le
  dsimp [A] at htotal ⊢
  calc
    |triangularIsingRaySymbolDeriv J b p q| <=
        (CD + 1) * |b - beta| + Cmom *
          ((1 - Real.cos p) + (1 - Real.cos q)) := htotal
    _ <= K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))) := by
      nlinarith [abs_nonneg (b - beta), hA]


end
end StatMech.FrontierA
