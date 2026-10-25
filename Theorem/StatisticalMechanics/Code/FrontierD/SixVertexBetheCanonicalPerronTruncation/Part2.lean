/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem lipschitzWith_sixVertexRegularizedBetheLogKernel
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    LipschitzWith (sixVertexRegularizedBetheLogLipschitzConstant c epsilon)
      (sixVertexRegularizedBetheLogKernel c epsilon) := by
  let A : Real :=
    (1 / 2 : Real) *
      ((2 * (c ^ 2 - 1)) / (c ^ 2 - 2) ^ 2 + 2 / epsilon)
  have hc2 : 0 < c ^ 2 - 2 := by
    have hcplus : 0 < c + 2 := by linarith
    nlinarith [mul_pos (sub_pos.mpr hc) hcplus]
  have hc1 : 0 <= 2 * (c ^ 2 - 1) := by nlinarith
  have hA : 0 <= A := by
    dsimp [A]
    exact mul_nonneg (by norm_num)
      (add_nonneg (div_nonneg hc1 (sq_nonneg _))
        (div_nonneg (by norm_num) hepsilon.le))
  let C : NNReal := sixVertexRegularizedBetheLogLipschitzConstant c epsilon
  change LipschitzWith C _
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hnum := abs_log_sub_log_le_of_lower
    (m := (c ^ 2 - 2) ^ 2)
    (pow_pos hc2 2)
    (sixVertexBetheLogNumerator_lower hc x)
    (sixVertexBetheLogNumerator_lower hc y)
  have hden := abs_log_sub_log_le_of_lower
    (m := epsilon)
    (x := sixVertexBetheLogDenominator x + epsilon)
    (y := sixVertexBetheLogDenominator y + epsilon) hepsilon
    (by
      have := sixVertexBetheLogDenominator_nonneg x
      linarith)
    (by
      have := sixVertexBetheLogDenominator_nonneg y
      linarith)
  have hnumDiff := abs_sixVertexBetheLogNumerator_sub_le hc x y
  have hdenDiff := abs_sixVertexBetheLogDenominator_sub_le x y
  rw [show (C : Real) = A by
    dsimp [C, sixVertexRegularizedBetheLogLipschitzConstant]
    exact Real.coe_toNNReal _ hA]
  change |sixVertexRegularizedBetheLogKernel c epsilon x -
      sixVertexRegularizedBetheLogKernel c epsilon y| <= A * |x - y|
  unfold sixVertexRegularizedBetheLogKernel
  have hnum' :
      |Real.log (sixVertexBetheLogNumerator c x) -
          Real.log (sixVertexBetheLogNumerator c y)| <=
        ((2 * (c ^ 2 - 1)) / (c ^ 2 - 2) ^ 2) * |x - y| := by
    calc
      _ <= |sixVertexBetheLogNumerator c x -
          sixVertexBetheLogNumerator c y| / (c ^ 2 - 2) ^ 2 := hnum
      _ <= (2 * (c ^ 2 - 1) * |x - y|) / (c ^ 2 - 2) ^ 2 :=
        div_le_div_of_nonneg_right hnumDiff (sq_nonneg _)
      _ = ((2 * (c ^ 2 - 1)) / (c ^ 2 - 2) ^ 2) * |x - y| := by
        ring
  have hden' :
      |Real.log (sixVertexBetheLogDenominator x + epsilon) -
          Real.log (sixVertexBetheLogDenominator y + epsilon)| <=
        (2 / epsilon) * |x - y| := by
    calc
      _ <= |(sixVertexBetheLogDenominator x + epsilon) -
          (sixVertexBetheLogDenominator y + epsilon)| / epsilon := hden
      _ = |sixVertexBetheLogDenominator x -
          sixVertexBetheLogDenominator y| / epsilon := by
        rw [show (sixVertexBetheLogDenominator x + epsilon) -
          (sixVertexBetheLogDenominator y + epsilon) =
          sixVertexBetheLogDenominator x -
            sixVertexBetheLogDenominator y by ring]
      _ <= (2 * |x - y|) / epsilon :=
        div_le_div_of_nonneg_right hdenDiff hepsilon.le
      _ = (2 / epsilon) * |x - y| := by ring
  calc
    |(1 / 2 : Real) *
        (Real.log (sixVertexBetheLogNumerator c x) -
          Real.log (sixVertexBetheLogDenominator x + epsilon)) -
      (1 / 2 : Real) *
        (Real.log (sixVertexBetheLogNumerator c y) -
          Real.log (sixVertexBetheLogDenominator y + epsilon))| =
      (1 / 2 : Real) *
        |(Real.log (sixVertexBetheLogNumerator c x) -
            Real.log (sixVertexBetheLogNumerator c y)) -
          (Real.log (sixVertexBetheLogDenominator x + epsilon) -
            Real.log (sixVertexBetheLogDenominator y + epsilon))| := by
        rw [← abs_of_nonneg (by norm_num : (0 : Real) <= 1 / 2),
          ← abs_mul]
        congr 1
        ring
    _ <= (1 / 2 : Real) *
        (|Real.log (sixVertexBetheLogNumerator c x) -
            Real.log (sixVertexBetheLogNumerator c y)| +
          |Real.log (sixVertexBetheLogDenominator x + epsilon) -
            Real.log (sixVertexBetheLogDenominator y + epsilon)|) := by
        gcongr
        exact abs_sub _ _
    _ <= (1 / 2 : Real) *
        ((((2 * (c ^ 2 - 1)) / (c ^ 2 - 2) ^ 2) * |x - y|) +
          ((2 / epsilon) * |x - y|)) := by gcongr
    _ = A * |x - y| := by dsimp [A]; ring

theorem exists_lipschitzWith_sixVertexRegularizedBetheLogKernel
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    ∃ C : NNReal,
      LipschitzWith C (sixVertexRegularizedBetheLogKernel c epsilon) :=
  ⟨sixVertexRegularizedBetheLogLipschitzConstant c epsilon,
    lipschitzWith_sixVertexRegularizedBetheLogKernel hc hepsilon⟩

theorem continuous_sixVertexRegularizedBetheLogKernel
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    Continuous (sixVertexRegularizedBetheLogKernel c epsilon) := by
  obtain ⟨C, hC⟩ :=
    exists_lipschitzWith_sixVertexRegularizedBetheLogKernel hc hepsilon
  exact hC.continuous

theorem periodic_sixVertexRegularizedBetheLogKernel
    (c epsilon : Real) :
    Function.Periodic (sixVertexRegularizedBetheLogKernel c epsilon)
      (2 * Real.pi) := by
  intro x
  unfold sixVertexRegularizedBetheLogKernel sixVertexBetheLogNumerator
    sixVertexBetheLogDenominator
  rw [Real.cos_add_two_pi]

theorem even_sixVertexRegularizedBetheLogKernel
    (c epsilon : Real) :
    Function.Even (sixVertexRegularizedBetheLogKernel c epsilon) := by
  intro x
  unfold sixVertexRegularizedBetheLogKernel sixVertexBetheLogNumerator
    sixVertexBetheLogDenominator
  rw [Real.cos_neg]


theorem sixVertexCanonicalDensityPerronEmpiricalRegularized_eq_positiveHalf
    {c : Real} (hc : 2 < c) (epsilon : Real) (k : Nat) :
    sixVertexCanonicalDensityPerronEmpiricalObservable hc
        (sixVertexRegularizedBetheLogKernel c epsilon) k =
      (2 * ∑ j : Fin (k + 1),
        sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j)) /
        (sixVertexFourWidth 0 k : Real) := by
  let p := sixVertexCanonicalDensityPerronBetheRoots hc k
  let q := sixVertexCanonicalDensityPerronPositiveHalfRoots hc k
  have hlift : sixVertexEvenSymmetricLift (k + 1) q = p := by
    exact sixVertexEvenSymmetricLift_projection (k + 1)
      (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k).2.1
  unfold sixVertexCanonicalDensityPerronEmpiricalObservable
  change (∑ j, sixVertexRegularizedBetheLogKernel c epsilon (p j)) /
      (sixVertexFourWidth 0 k : Real) =
    (2 * ∑ j, sixVertexRegularizedBetheLogKernel c epsilon (q j)) /
      (sixVertexFourWidth 0 k : Real)
  rw [← hlift, Fin.sum_univ_add]
  apply congrArg (fun z : Real => z / (sixVertexFourWidth 0 k : Real))
  have hneg :
      (∑ j : Fin (k + 1), sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenSymmetricLift (k + 1) q
          (Fin.castAdd (k + 1) j))) =
      ∑ j : Fin (k + 1),
        sixVertexRegularizedBetheLogKernel c epsilon (q j) := by
    rw [show (∑ j : Fin (k + 1),
        sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexEvenSymmetricLift (k + 1) q
            (Fin.castAdd (k + 1) j))) =
        ∑ j : Fin (k + 1),
          sixVertexRegularizedBetheLogKernel c epsilon (q j.rev) by
      apply Finset.sum_congr rfl
      intro j hj
      rw [sixVertexEvenSymmetricLift_castAdd]
      exact even_sixVertexRegularizedBetheLogKernel c epsilon (q j.rev)]
    simpa using (Equiv.sum_comp Fin.revPerm
      (fun j : Fin (k + 1) =>
        sixVertexRegularizedBetheLogKernel c epsilon (q j)))
  have hpos :
      (∑ j : Fin (k + 1), sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexEvenSymmetricLift (k + 1) q
          (Fin.natAdd (k + 1) j))) =
      ∑ j : Fin (k + 1),
        sixVertexRegularizedBetheLogKernel c epsilon (q j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [sixVertexEvenSymmetricLift_natAdd]
  rw [hneg, hpos]
  ring

theorem sixVertexBetheM_log_norm_eq_logNumerator_sub_logDenominator
    {c p : Real} (hc : 2 < c) (hp : sixVertexBethePhase p ≠ 1) :
    Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖ =
      (1 / 2 : Real) *
        (Real.log (sixVertexBetheLogNumerator c p) -
          Real.log (sixVertexBetheLogDenominator p)) := by
  have hden : 0 < sixVertexBetheLogDenominator p := by
    have hratio := sixVertexBetheM_phase_normSq c p hp
    have hratioPos : 0 <
        sixVertexBetheLogNumerator c p /
          sixVertexBetheLogDenominator p := by
      unfold sixVertexBetheLogNumerator sixVertexBetheLogDenominator
      rw [← hratio]
      exact Complex.normSq_pos.mpr (sixVertexBetheM_phase_ne_zero hc p)
    rcases (div_pos_iff.mp hratioPos) with h | h
    · exact h.2
    · linarith [sixVertexBetheLogNumerator_pos hc p]
  rw [sixVertexBetheM_phase_log_norm c p hp]
  have hnum' : 0 < (c ^ 2 - 1) ^ 2 + 1 +
      2 * (c ^ 2 - 1) * Real.cos p := by
    simpa only [sixVertexBetheLogNumerator] using
      sixVertexBetheLogNumerator_pos hc p
  have hden' : 0 < 2 - 2 * Real.cos p := by
    simpa only [sixVertexBetheLogDenominator] using hden
  unfold sixVertexBetheLogNumerator sixVertexBetheLogDenominator
  rw [Real.log_div hnum'.ne' hden'.ne']


theorem sixVertexRegularizedBetheLogKernel_error_bounds
    {c p epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hp : sixVertexBethePhase p ≠ 1) :
    0 <= Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖ -
        sixVertexRegularizedBetheLogKernel c epsilon p ∧
      Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖ -
          sixVertexRegularizedBetheLogKernel c epsilon p <=
        epsilon / (2 * sixVertexBetheLogDenominator p) := by
  have hden : 0 < sixVertexBetheLogDenominator p := by
    have hratio := sixVertexBetheM_phase_normSq c p hp
    have hratioPos : 0 <
        sixVertexBetheLogNumerator c p /
          sixVertexBetheLogDenominator p := by
      unfold sixVertexBetheLogNumerator sixVertexBetheLogDenominator
      rw [← hratio]
      exact Complex.normSq_pos.mpr (sixVertexBetheM_phase_ne_zero hc p)
    rcases (div_pos_iff.mp hratioPos) with h | h
    · exact h.2
    · linarith [sixVertexBetheLogNumerator_pos hc p]
  have hdeneps : 0 < sixVertexBetheLogDenominator p + epsilon :=
    add_pos hden hepsilon
  rw [sixVertexBetheM_log_norm_eq_logNumerator_sub_logDenominator hc hp]
  unfold sixVertexRegularizedBetheLogKernel
  have herr :
      (1 / 2 : Real) *
          (Real.log (sixVertexBetheLogNumerator c p) -
            Real.log (sixVertexBetheLogDenominator p)) -
        (1 / 2 : Real) *
          (Real.log (sixVertexBetheLogNumerator c p) -
            Real.log (sixVertexBetheLogDenominator p + epsilon)) =
      (1 / 2 : Real) * Real.log
        ((sixVertexBetheLogDenominator p + epsilon) /
          sixVertexBetheLogDenominator p) := by
    rw [Real.log_div hdeneps.ne' hden.ne']
    ring
  rw [herr]
  constructor
  · apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    rw [le_div_iff₀ hden]
    linarith
  · have hlog := Real.log_le_sub_one_of_pos
      (div_pos hdeneps hden)
    have hrewrite :
        (sixVertexBetheLogDenominator p + epsilon) /
            sixVertexBetheLogDenominator p - 1 =
          epsilon / sixVertexBetheLogDenominator p := by
      field_simp [hden.ne'] <;> ring
    rw [hrewrite] at hlog
    calc
      (1 / 2 : Real) * Real.log
          ((sixVertexBetheLogDenominator p + epsilon) /
            sixVertexBetheLogDenominator p) <=
        (1 / 2 : Real) *
          (epsilon / sixVertexBetheLogDenominator p) := by gcongr
      _ = epsilon / (2 * sixVertexBetheLogDenominator p) := by ring

theorem sixVertexRegularizedBetheLogKernel_nonneg
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hepsilonUpper : epsilon <= (c ^ 2 - 2) ^ 2 - 4) (p : Real) :
    0 <= sixVertexRegularizedBetheLogKernel c epsilon p := by
  have hnumPos := sixVertexBetheLogNumerator_pos hc p
  have hdenNonneg := sixVertexBetheLogDenominator_nonneg p
  have hdenLe : sixVertexBetheLogDenominator p <= 4 := by
    unfold sixVertexBetheLogDenominator
    linarith [Real.neg_one_le_cos p]
  have hdeneps : 0 < sixVertexBetheLogDenominator p + epsilon :=
    add_pos_of_nonneg_of_pos hdenNonneg hepsilon
  have hle : sixVertexBetheLogDenominator p + epsilon <=
      sixVertexBetheLogNumerator c p := by
    have hnumLower := sixVertexBetheLogNumerator_lower hc p
    linarith
  unfold sixVertexRegularizedBetheLogKernel
  exact mul_nonneg (by norm_num)
    (sub_nonneg.mpr (Real.log_le_log hdeneps hle))


theorem sixVertexCanonicalDensityPerronLogDenominator_quantile_lower
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    4 * (2 * (j : Real) + 1) ^ 2 <=
      (sixVertexFourWidth 0 k : Real) ^ 2 *
        sixVertexBetheLogDenominator
          (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j) := by
  let p := sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j
  let N : Real := sixVertexFourWidth 0 k
  let s : Real := 2 * (j : Real) + 1
  have hp := (sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo
    hc k j).1
  have hpPi := (sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo
    hc k j).2
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hs : 0 < s := by dsimp [s]; positivity
  have habsp : |p| <= Real.pi := by
    rw [abs_of_pos hp]
    exact hpPi.le
  have hcos := Real.cos_le_one_sub_mul_cos_sq habsp
  have hdenP : 4 * p ^ 2 <= Real.pi ^ 2 *
      sixVertexBetheLogDenominator p := by
    have hcos' := mul_le_mul_of_nonneg_left hcos (sq_nonneg Real.pi)
    field_simp [Real.pi_ne_zero] at hcos'
    unfold sixVertexBetheLogDenominator
    nlinarith
  have hquant :=
    sixVertexCanonicalDensityPerronPositiveHalfRoots_quantile_lower hc k j
  change Real.pi * s < N * p at hquant
  have hquantSq : Real.pi ^ 2 * s ^ 2 <= N ^ 2 * p ^ 2 := by
    have hleft : 0 <= Real.pi * s := by positivity
    have hright : 0 <= N * p := by positivity
    nlinarith [(sq_le_sq₀ hleft hright).2 hquant.le]
  have hNnonneg : 0 <= N ^ 2 := sq_nonneg N
  have h1 := mul_le_mul_of_nonneg_left hdenP hNnonneg
  have h2 := mul_le_mul_of_nonneg_left hquantSq
    (by norm_num : (0 : Real) <= 4)
  change 4 * s ^ 2 <= N ^ 2 * sixVertexBetheLogDenominator p
  nlinarith [sq_pos_of_pos Real.pi_pos]


theorem sum_Ico_inv_odd_sq_le_inv (J K : Nat) (hJ : 0 < J) :
    (∑ j ∈ Finset.Ico J K,
      (1 : Real) / (2 * (j : Real) + 1) ^ 2) <=
        1 / (J : Real) := by
  by_cases hJK : J <= K
  · calc
      _ <= ∑ j ∈ Finset.Ico J K,
          ((1 : Real) / (j : Real) -
            1 / ((j + 1 : Nat) : Real)) := by
        apply Finset.sum_le_sum
        intro j hjmem
        have hjNat : J <= j := (Finset.mem_Ico.mp hjmem).1
        have hj : (0 : Real) < j := by
          exact_mod_cast hJ.trans_le hjNat
        have hprod : (0 : Real) <
            (j : Real) * ((j + 1 : Nat) : Real) := by positivity
        have hden : (j : Real) * ((j + 1 : Nat) : Real) <=
            (2 * (j : Real) + 1) ^ 2 := by
          push_cast
          nlinarith [sq_nonneg (j : Real)]
        calc
          (1 : Real) / (2 * (j : Real) + 1) ^ 2 <=
              1 / ((j : Real) * ((j + 1 : Nat) : Real)) :=
            one_div_le_one_div_of_le hprod hden
          _ = 1 / (j : Real) - 1 / ((j + 1 : Nat) : Real) := by
            push_cast
            field_simp [hj.ne']
            ring
      _ = 1 / (J : Real) - 1 / (K : Real) := by
        rw [Finset.sum_Ico_eq_sub _ hJK,
          Finset.sum_range_sub'
            (fun j : Nat => (1 : Real) / (j : Real)),
          Finset.sum_range_sub'
            (fun j : Nat => (1 : Real) / (j : Real))]
        ring
      _ <= 1 / (J : Real) := sub_le_self _ (by positivity)
  · rw [Finset.Ico_eq_empty (fun hlt => hJK hlt.le)]
    simp

theorem sixVertexCanonicalDensityPerronRootAverage_sub_regularized_eq
    {c : Real} (hc : 2 < c) (epsilon : Real) (k : Nat) :
    sixVertexSymmetricBetheRootAverage c
        (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k -
      sixVertexCanonicalDensityPerronEmpiricalObservable hc
        (sixVertexRegularizedBetheLogKernel c epsilon) k =
      (2 * ∑ j : Fin (k + 1),
        (Real.log ‖sixVertexBetheM c (sixVertexBethePhase
            (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ -
          sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))) /
        (sixVertexFourWidth 0 k : Real) := by
  rw [sixVertexCanonicalDensityPerronEmpiricalRegularized_eq_positiveHalf]
  unfold sixVertexSymmetricBetheRootAverage
    sixVertexCanonicalDensityPerronPositiveHalfRootFamily
  rw [Finset.sum_sub_distrib]
  ring

theorem sixVertexCanonicalDensityPerronRegularized_pointwise_error_le
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (k : Nat) (j : Fin (k + 1)) :
    Real.log ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ -
      sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j) <=
      epsilon * (sixVertexFourWidth 0 k : Real) ^ 2 /
        (8 * (2 * (j : Real) + 1) ^ 2) := by
  let p := sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j
  let N : Real := sixVertexFourWidth 0 k
  let s : Real := 2 * (j : Real) + 1
  have hphase : sixVertexBethePhase p ≠ 1 := by
    exact SixVertexOpenRootSimplex.phase_ne_one_of_even
      (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
      (Fin.natAdd (k + 1) j)
  have herror :=
    (sixVertexRegularizedBetheLogKernel_error_bounds hc hepsilon hphase).2
  have hden : 0 < sixVertexBetheLogDenominator p := by
    have hratio := sixVertexBetheM_phase_normSq c p hphase
    have hratioPos : 0 < sixVertexBetheLogNumerator c p /
        sixVertexBetheLogDenominator p := by
      unfold sixVertexBetheLogNumerator sixVertexBetheLogDenominator
      rw [← hratio]
      exact Complex.normSq_pos.mpr (sixVertexBetheM_phase_ne_zero hc p)
    rcases (div_pos_iff.mp hratioPos) with h | h
    · exact h.2
    · linarith [sixVertexBetheLogNumerator_pos hc p]
  have hs : 0 < s := by dsimp [s]; positivity
  have hquant :=
    sixVertexCanonicalDensityPerronLogDenominator_quantile_lower hc k j
  change 4 * s ^ 2 <= N ^ 2 * sixVertexBetheLogDenominator p at hquant
  have hinv : 1 / sixVertexBetheLogDenominator p <=
      N ^ 2 / (4 * s ^ 2) := by
    field_simp [hden.ne', hs.ne']
    nlinarith
  change Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖ -
      sixVertexRegularizedBetheLogKernel c epsilon p <=
    epsilon * N ^ 2 / (8 * s ^ 2)
  calc
    _ <= epsilon / (2 * sixVertexBetheLogDenominator p) := herror
    _ = (epsilon / 2) *
        (1 / sixVertexBetheLogDenominator p) := by ring
    _ <= (epsilon / 2) * (N ^ 2 / (4 * s ^ 2)) := by
      gcongr
    _ = epsilon * N ^ 2 / (8 * s ^ 2) := by ring

theorem sixVertexCanonicalDensityPerronRegularized_tail_error_le
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    {J : Nat} (hJ : 0 < J) (k : Nat) :
    (2 * ∑ j : Fin (k + 1) with J <= j.val,
      (Real.log ‖sixVertexBetheM c (sixVertexBethePhase
          (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ -
        sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))) /
        (sixVertexFourWidth 0 k : Real) <=
      epsilon * (sixVertexFourWidth 0 k : Real) / (4 * (J : Real)) := by
  let N : Real := sixVertexFourWidth 0 k
  let d : Fin (k + 1) -> Real := fun j =>
    Real.log ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ -
      sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j)
  let w : Nat -> Real := fun j => (1 : Real) / (2 * (j : Real) + 1) ^ 2
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hindex :
      (∑ j : Fin (k + 1) with J <= j.val, w j.val) =
        ∑ i ∈ Finset.Ico J (k + 1), w i := by
    apply Finset.sum_bij (fun j _ => j.val)
    · intro j hj
      exact Finset.mem_Ico.mpr
        ⟨(Finset.mem_filter.mp hj).2, j.isLt⟩
    · intro a ha b hb hab
      exact Fin.ext hab
    · intro i hi
      have hi' := Finset.mem_Ico.mp hi
      let j : Fin (k + 1) := ⟨i, hi'.2⟩
      refine ⟨j, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'.1⟩
    · intro j hj
      rfl
  have hsum : (∑ j : Fin (k + 1) with J <= j.val, d j) <=
      (epsilon * N ^ 2 / 8) * (1 / (J : Real)) := by
    calc
      _ <= ∑ j : Fin (k + 1) with J <= j.val,
          (epsilon * N ^ 2 / 8) * w j.val := by
        apply Finset.sum_le_sum
        intro j hj
        have hpoint :=
          sixVertexCanonicalDensityPerronRegularized_pointwise_error_le
            hc hepsilon k j
        dsimp [d, w, N]
        calc
          _ <= epsilon * (sixVertexFourWidth 0 k : Real) ^ 2 /
              (8 * (2 * (j : Real) + 1) ^ 2) := hpoint
          _ = (epsilon * (sixVertexFourWidth 0 k : Real) ^ 2 / 8) *
              (1 / (2 * (j : Real) + 1) ^ 2) := by
            have hs : (0 : Real) < 2 * (j : Real) + 1 := by positivity
            field_simp [hs.ne']
      _ = (epsilon * N ^ 2 / 8) *
          (∑ j : Fin (k + 1) with J <= j.val, w j.val) := by
        rw [Finset.mul_sum]
      _ = (epsilon * N ^ 2 / 8) *
          (∑ i ∈ Finset.Ico J (k + 1), w i) := by rw [hindex]
      _ <= (epsilon * N ^ 2 / 8) * (1 / (J : Real)) := by
        gcongr
        exact sum_Ico_inv_odd_sq_le_inv J (k + 1) hJ
  change (2 * ∑ j : Fin (k + 1) with J <= j.val, d j) / N <=
    epsilon * N / (4 * (J : Real))
  calc
    (2 * ∑ j : Fin (k + 1) with J <= j.val, d j) / N <=
        (2 * ((epsilon * N ^ 2 / 8) * (1 / (J : Real)))) / N := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (by norm_num)) hN.le
    _ = epsilon * N / (4 * (J : Real)) := by
      have hJreal : (0 : Real) < J := by exact_mod_cast hJ
      field_simp [hN.ne', hJreal.ne']
      ring


theorem sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hepsilonUpper : epsilon <= (c ^ 2 - 2) ^ 2 - 4)
    {J : Nat} (hJ : 0 < J) (k : Nat) :
    0 <= sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k -
        sixVertexCanonicalDensityPerronEmpiricalObservable hc
          (sixVertexRegularizedBetheLogKernel c epsilon) k ∧
      sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k -
        sixVertexCanonicalDensityPerronEmpiricalObservable hc
          (sixVertexRegularizedBetheLogKernel c epsilon) k <=
        sixVertexCanonicalDensityPerronInitialLogContribution hc J k +
          epsilon * (sixVertexFourWidth 0 k : Real) / (4 * (J : Real)) := by
  let N : Real := sixVertexFourWidth 0 k
  let raw : Fin (k + 1) -> Real := fun j =>
    Real.log ‖sixVertexBetheM c (sixVertexBethePhase
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖
  let reg : Fin (k + 1) -> Real := fun j =>
    sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j)
  let d : Fin (k + 1) -> Real := fun j => raw j - reg j
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hphase (j : Fin (k + 1)) :
      sixVertexBethePhase
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j) ≠ 1 := by
    exact SixVertexOpenRootSimplex.phase_ne_one_of_even
      (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
      (Fin.natAdd (k + 1) j)
  have hdNonneg (j : Fin (k + 1)) : 0 <= d j := by
    exact (sixVertexRegularizedBetheLogKernel_error_bounds hc hepsilon
      (hphase j)).1
  have hregNonneg (j : Fin (k + 1)) : 0 <= reg j := by
    exact sixVertexRegularizedBetheLogKernel_nonneg hc hepsilon
      hepsilonUpper _
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (k + 1))) (fun j => j.val < J) d
  simp only [not_lt] at hsplit
  have hedge : (∑ j : Fin (k + 1) with j.val < J, d j) <=
      ∑ j : Fin (k + 1) with j.val < J, raw j := by
    apply Finset.sum_le_sum
    intro j hj
    dsimp [d]
    linarith [hregNonneg j]
  have hedgeScaled :
      (2 * ∑ j : Fin (k + 1) with j.val < J, d j) / N <=
        sixVertexCanonicalDensityPerronInitialLogContribution hc J k := by
    unfold sixVertexCanonicalDensityPerronInitialLogContribution
    change (2 * ∑ j : Fin (k + 1) with j.val < J, d j) / N <=
      (2 * ∑ j : Fin (k + 1) with j.val < J, raw j) / N
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hedge (by norm_num)) hN.le
  have htail :=
    sixVertexCanonicalDensityPerronRegularized_tail_error_le
      hc hepsilon hJ k
  change (2 * ∑ j : Fin (k + 1) with J <= j.val, d j) / N <=
    epsilon * N / (4 * (J : Real)) at htail
  rw [sixVertexCanonicalDensityPerronRootAverage_sub_regularized_eq]
  change 0 <= (2 * ∑ j, d j) / N ∧
    (2 * ∑ j, d j) / N <=
      sixVertexCanonicalDensityPerronInitialLogContribution hc J k +
        epsilon * N / (4 * (J : Real))
  constructor
  · apply div_nonneg
    · exact mul_nonneg (by norm_num)
        (Finset.sum_nonneg (fun j _ => hdNonneg j))
    · exact hN.le
  · calc
      (2 * ∑ j, d j) / N =
          (2 * ∑ j : Fin (k + 1) with j.val < J, d j) / N +
            (2 * ∑ j : Fin (k + 1) with J <= j.val, d j) / N := by
        rw [← hsplit]
        ring
      _ <= sixVertexCanonicalDensityPerronInitialLogContribution hc J k +
          epsilon * N / (4 * (J : Real)) := add_le_add hedgeScaled htail


end
end StatMech.FrontierD
