/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalSecond.Part2
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

theorem hasDerivAt_triangularIsingRayLogDeriv
    {J beta p q : Real}
    (hne : triangularIsingSymbol beta beta (beta * J) p q ≠ 0) :
    HasDerivAt (fun b => triangularIsingRayLogDeriv J b p q)
      (triangularIsingRayLogDeriv2 J beta p q) beta := by
  unfold triangularIsingRayLogDeriv triangularIsingRayLogDeriv2
  convert (hasDerivAt_triangularIsingRaySymbolDeriv J beta p q).div
    (hasDerivAt_triangularIsingSymbol_along_ray J beta p q) hne using 1
  all_goals simp [pow_two]

theorem triangularIsingRaySymbolDeriv2_zero_pos_at_root
    {beta J : Real} (hbeta : 0 < beta) (hJ : -1 < J)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    0 < triangularIsingRaySymbolDeriv2 J beta 0 0 := by
  let P := triangularIsingCriticalPolynomialAlong J
  let H := triangularIsingZeroModePrefactorAlong J
  let F : Real -> Real := fun b =>
    triangularIsingSymbol b b (b * J) 0 0
  have htanh : ContDiff Real 2 Real.tanh := by
    have heq : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
      funext x
      exact Real.tanh_eq_sinh_div_cosh x
    rw [heq]
    exact Real.contDiff_sinh.div Real.contDiff_cosh
      (fun x => (Real.cosh_pos x).ne')
  have hP2 : ContDiffAt Real 2 P beta := by
    unfold P triangularIsingCriticalPolynomialAlong
      triangularIsingCriticalPolynomial
    fun_prop
  have hH2 : ContDiffAt Real 2 H beta := by
    unfold H triangularIsingZeroModePrefactorAlong
    fun_prop
  have hPzero : P beta = 0 :=
    (triangularIsingCriticalPolynomial_zero_iff_rate_eq_one hbeta).2 hroot
  have hFeq : F = fun b => P b ^ 2 * H b := by
    funext b
    exact triangularIsing_zeroMode_eq_polynomialAlong_sq_mul J b
  have hD1eq : (fun b => triangularIsingRaySymbolDeriv J b 0 0) = deriv F := by
    funext b
    simpa only [F] using
      (hasDerivAt_triangularIsingSymbol_along_ray J b 0 0).deriv.symm
  have hsecond : iteratedDeriv 2 F beta =
      2 * deriv P beta ^ 2 * H beta := by
    rw [hFeq]
    have hfun : (fun b => P b ^ 2 * H b) = (P * P) * H := by
      funext b
      simp only [Pi.mul_apply]
      ring
    rw [hfun]
    have hPP1 : iteratedDeriv 1 (P * P) beta = 0 := by
      rw [iteratedDeriv_mul (n := 1) (x := beta)
        (hP2.of_le (by norm_num)) (hP2.of_le (by norm_num))]
      norm_num [Finset.sum_range_succ, iteratedDeriv_zero,
        iteratedDeriv_one, hPzero]
    have hPP2 : iteratedDeriv 2 (P * P) beta =
        2 * deriv P beta ^ 2 := by
      rw [iteratedDeriv_mul (n := 2) (x := beta) hP2 hP2]
      norm_num [Finset.sum_range_succ, iteratedDeriv_zero,
        iteratedDeriv_one, hPzero]
      ring
    have hPP1' : iteratedDeriv 1 (fun x => P x * P x) beta = 0 := by
      simpa only [Pi.mul_apply] using hPP1
    have hPP2' : iteratedDeriv 2 (fun x => P x * P x) beta =
        2 * deriv P beta ^ 2 := by
      simpa only [Pi.mul_apply] using hPP2
    have hmul := iteratedDeriv_mul (n := 2) (x := beta)
      (hP2.mul hP2) hH2
    change iteratedDeriv 2 ((fun x => P x * P x) * H) beta = _
    rw [hmul]
    norm_num [Finset.sum_range_succ, hPP1', hPP2',
      iteratedDeriv_zero, hPzero]
  unfold triangularIsingRaySymbolDeriv2
  rw [hD1eq]
  have hiter : deriv (deriv F) beta = iteratedDeriv 2 F beta := by
    rw [show (2 : Nat) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]
  rw [hiter, hsecond]
  have hPneg := deriv_triangularIsingCriticalPolynomialAlong_neg_at_root
    hbeta hJ hroot
  have hHpos : 0 < H beta := by
    unfold H triangularIsingZeroModePrefactorAlong
    positivity
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_neg hPneg)) hHpos

theorem triangularIsingRaySymbolDeriv2_sub_zero
    (J beta p q : Real) :
    triangularIsingRaySymbolDeriv2 J beta p q -
        triangularIsingRaySymbolDeriv2 J beta 0 0 =
      4 * Real.sinh (2 * beta) *
          ((1 - Real.cos p) + (1 - Real.cos q)) +
        4 * J ^ 2 * Real.sinh (2 * beta * J) *
          (1 - Real.cos (p + q)) := by
  have hlin : HasDerivAt (fun b : Real => 2 * b) 2 beta := by
    convert (hasDerivAt_id beta).const_mul 2 using 1 <;> ring
  have hlinJ : HasDerivAt (fun b : Real => 2 * b * J) (2 * J) beta := by
    convert ((hasDerivAt_id beta).const_mul 2).mul_const J using 1 <;> ring
  have hC := (Real.hasDerivAt_cosh (2 * beta)).comp beta hlin
  have hCJ := (Real.hasDerivAt_cosh (2 * beta * J)).comp beta hlinJ
  let A := (1 - Real.cos p) + (1 - Real.cos q)
  let B := 1 - Real.cos (p + q)
  have hright : HasDerivAt
      (fun b => 2 * Real.cosh (2 * b) * A +
        2 * J * Real.cosh (2 * b * J) * B)
      (4 * Real.sinh (2 * beta) * A +
        4 * J ^ 2 * Real.sinh (2 * beta * J) * B) beta := by
    convert ((hC.const_mul 2).mul_const A).add
      (((hCJ.const_mul (2 * J)).mul_const B)) using 1 <;> ring
  have hleft := (hasDerivAt_triangularIsingRaySymbolDeriv J beta p q).sub
    (hasDerivAt_triangularIsingRaySymbolDeriv J beta 0 0)
  have hleft' : HasDerivAt
      (fun b => triangularIsingRaySymbolDeriv J b p q -
        triangularIsingRaySymbolDeriv J b 0 0)
      (triangularIsingRaySymbolDeriv2 J beta p q -
        triangularIsingRaySymbolDeriv2 J beta 0 0) beta := by
    simpa only [Pi.sub_apply] using hleft
  have hfun : (fun b => triangularIsingRaySymbolDeriv J b p q -
      triangularIsingRaySymbolDeriv J b 0 0) =
      fun b => 2 * Real.cosh (2 * b) * A +
        2 * J * Real.cosh (2 * b * J) * B := by
    funext b
    exact triangularIsingRaySymbolDeriv_sub_zero J b p q
  rw [hfun] at hleft'
  simpa only [A, B] using hleft'.unique hright

theorem triangularIsingRayLogDeriv2_eq
    {J beta p q : Real}
    (hne : triangularIsingSymbol beta beta (beta * J) p q ≠ 0) :
    triangularIsingRayLogDeriv2 J beta p q =
      triangularIsingRaySymbolDeriv2 J beta p q /
          triangularIsingSymbol beta beta (beta * J) p q -
        (triangularIsingRaySymbolDeriv J beta p q /
          triangularIsingSymbol beta beta (beta * J) p q) ^ 2 := by
  unfold triangularIsingRayLogDeriv2
  field_simp [hne]

set_option maxHeartbeats 800000 in

theorem exists_triangularIsingRayLogDeriv2_lower_at_root
    {beta J : Real} (hbeta : 0 < beta) (hJ : -1 < J)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    ∃ a C : Real, 0 < a ∧ 0 <= C ∧ ∀ p q : Real,
      |p| <= Real.pi -> |q| <= Real.pi -> (p ≠ 0 ∨ q ≠ 0) ->
      a * triangularIsingCriticalInverseSymbol beta J p q - C <=
        triangularIsingRayLogDeriv2 J beta p q := by
  obtain ⟨U, hUnhds, _hUopen, m, K, hm, hK, hbounds⟩ :=
    exists_triangularIsingCriticalRay_local_bounds hbeta hJ hroot
  have hbetaU : beta ∈ U := mem_of_mem_nhds hUnhds
  let a := triangularIsingRaySymbolDeriv2 J beta 0 0
  let L := 4 * |Real.sinh (2 * beta)| +
    8 * J ^ 2 * |Real.sinh (2 * beta * J)|
  let C := L / m + (K / m) ^ 2
  have ha : 0 < a :=
    triangularIsingRaySymbolDeriv2_zero_pos_at_root hbeta hJ hroot
  have hL : 0 <= L := by unfold L; positivity
  have hC : 0 <= C := by unfold C; positivity
  refine ⟨a, C, ha, hC, ?_⟩
  intro p q hp hq hne
  let A := (1 - Real.cos p) + (1 - Real.cos q)
  let B := 1 - Real.cos (p + q)
  let S := triangularIsingSymbol beta beta (beta * J) p q
  let D1 := triangularIsingRaySymbolDeriv J beta p q
  let D2 := triangularIsingRaySymbolDeriv2 J beta p q
  have hA : 0 < A := by
    have hAnonneg : 0 <= A := by
      unfold A
      nlinarith [Real.cos_le_one p, Real.cos_le_one q]
    apply lt_of_le_of_ne hAnonneg
    intro hzero
    have hpDef : 1 - Real.cos p = 0 := by
      have hp0 : 0 <= 1 - Real.cos p := by linarith [Real.cos_le_one p]
      have hq0 : 0 <= 1 - Real.cos q := by linarith [Real.cos_le_one q]
      unfold A at hzero
      nlinarith
    have hqDef : 1 - Real.cos q = 0 := by
      have hp0 : 0 <= 1 - Real.cos p := by linarith [Real.cos_le_one p]
      have hq0 : 0 <= 1 - Real.cos q := by linarith [Real.cos_le_one q]
      unfold A at hzero
      nlinarith
    have hpzero : p = 0 := by
      have hcosp : Real.cos p = 1 := by linarith
      exact (Real.cos_eq_one_iff_of_lt_of_lt
        (by rw [abs_le] at hp; linarith [Real.pi_pos])
        (by rw [abs_le] at hp; linarith [Real.pi_pos])).mp hcosp
    have hqzero : q = 0 := by
      have hcosq : Real.cos q = 1 := by linarith
      exact (Real.cos_eq_one_iff_of_lt_of_lt
        (by rw [abs_le] at hq; linarith [Real.pi_pos])
        (by rw [abs_le] at hq; linarith [Real.pi_pos])).mp hcosq
    exact hne.elim (fun hpne => hpne hpzero) (fun hqne => hqne hqzero)
  have hS : 0 < S := by
    dsimp [S]
    exact triangularIsingSymbol_pos_at_root_of_ne_zero hbeta hroot hp hq hne
  have hbase := (hbounds beta hbetaU p q).1
  have hbase' : m * A <= S := by
    simpa [A, S] using hbase
  have hD1 := (hbounds beta hbetaU p q).2
  have hD1' : |D1| <= K * A := by
    simpa only [sub_self, abs_zero, mul_zero, zero_add, A, D1] using hD1
  have hB0 : 0 <= B := by unfold B; linarith [Real.cos_le_one (p + q)]
  have hBA : B <= 2 * A := one_sub_cos_add_le_two_sum p q
  have hdiff := triangularIsingRaySymbolDeriv2_sub_zero J beta p q
  have herr : |D2 - a| <= L * A := by
    dsimp [D2, a]
    rw [hdiff]
    have h1 : |4 * Real.sinh (2 * beta) * A| <=
        4 * |Real.sinh (2 * beta)| * A := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 4),
        abs_of_pos hA]
    have h2 : |4 * J ^ 2 * Real.sinh (2 * beta * J) * B| <=
        8 * J ^ 2 * |Real.sinh (2 * beta * J)| * A := by
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : Real) <= 4), abs_of_nonneg (sq_nonneg J),
        abs_of_nonneg hB0]
      nlinarith [mul_nonneg (sq_nonneg J)
        (abs_nonneg (Real.sinh (2 * beta * J)))]
    calc
      |_ + _| <= |4 * Real.sinh (2 * beta) * A| +
          |4 * J ^ 2 * Real.sinh (2 * beta * J) * B| := abs_add_le _ _
      _ <= L * A := by unfold L; nlinarith
  have hAS : A / S <= 1 / m := by
    rw [div_le_div_iff₀ hS hm]
    nlinarith [hbase']
  have hD1ratio : |D1 / S| <= K / m := by
    rw [abs_div, abs_of_pos hS]
    apply (div_le_div_iff₀ hS hm).2
    nlinarith [hD1', hbase', hK.le]
  have hsq : (D1 / S) ^ 2 <= (K / m) ^ 2 := by
    have hKm : 0 <= K / m := div_nonneg hK.le hm.le
    have hsquare := (sq_le_sq₀ (abs_nonneg (D1 / S)) hKm).2 hD1ratio
    simpa only [sq_abs] using hsquare
  have herrdiv : -L / m <= (D2 - a) / S := by
    have herrLower : -L * A <= D2 - a := by
      have hlower := neg_le_of_abs_le herr
      linarith
    have hdiv : (-L * A) / S <= (D2 - a) / S :=
      div_le_div_of_nonneg_right herrLower hS.le
    have hLA : L * (A / S) <= L * (1 / m) :=
      mul_le_mul_of_nonneg_left hAS hL
    calc
      -L / m = -(L * (1 / m)) := by ring
      _ <= -(L * (A / S)) := neg_le_neg hLA
      _ = (-L * A) / S := by ring
      _ <= _ := hdiv
  have heq := triangularIsingRayLogDeriv2_eq (J := J) (beta := beta)
    (p := p) (q := q) hS.ne'
  rw [heq]
  unfold triangularIsingCriticalInverseSymbol
  have hsplit : triangularIsingRaySymbolDeriv2 J beta p q /
      triangularIsingSymbol beta beta (beta * J) p q =
      triangularIsingRaySymbolDeriv2 J beta 0 0 /
          triangularIsingSymbol beta beta (beta * J) p q +
        (triangularIsingRaySymbolDeriv2 J beta p q -
          triangularIsingRaySymbolDeriv2 J beta 0 0) /
          triangularIsingSymbol beta beta (beta * J) p q := by ring
  rw [hsplit]
  change a * (1 / S) - C <=
    a / S + (D2 - a) / S - (D1 / S) ^ 2
  calc
    a * (1 / S) - C = a / S - L / m - (K / m) ^ 2 := by
      dsimp [C]
      ring
    _ <= a / S + (D2 - a) / S - (D1 / S) ^ 2 := by
      have hfirst : a / S - L / m <= a / S + (D2 - a) / S := by
        calc
          a / S - L / m = a / S + (-L / m) := by ring
          _ <= a / S + (D2 - a) / S := add_le_add_right herrdiv (a / S)
      have hsecond : -(K / m) ^ 2 <= -(D1 / S) ^ 2 := neg_le_neg hsq
      exact add_le_add hfirst hsecond


end
end StatMech.FrontierA
