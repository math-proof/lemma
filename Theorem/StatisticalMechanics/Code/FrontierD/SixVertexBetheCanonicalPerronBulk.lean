/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexEvenPositiveHalfProjection_quantile_lower
    {c : Real} (hc : 2 < c) {k : Nat}
    {p : Fin ((k + 1) + (k + 1)) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1)) p) (j : Fin (k + 1)) :
    Real.pi * (2 * (j : Real) + 1) <
      (sixVertexFourWidth 0 k : Real) *
        sixVertexEvenPositiveHalfProjection (k + 1) p j := by
  let i : Fin ((k + 1) + (k + 1)) := Fin.natAdd (k + 1) j
  have hrevlt : i.rev < i := by
    rw [Fin.lt_def]
    dsimp [i]
    omega
  have hspace := sixVertexBetheSolution_quantumSpacing hc hopen hsol hrevlt
  have hsymm := hopen.2.1 i
  have hI : sixVertexCentralQuantumNumber i -
      sixVertexCentralQuantumNumber i.rev = 2 * (j : Real) + 1 := by
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp only [Fin.rev, Fin.val_mk]
    dsimp [i]
    have hjle : j.val ≤ k := by omega
    have hnat : k + 1 + (k + 1) - (k + 1 + j.val + 1) =
        k - j.val := by omega
    rw [hnat]
    push_cast [Nat.cast_sub hjle]
    ring
  rw [hI, hsymm] at hspace
  change Real.pi * (2 * (j : Real) + 1) <
    (sixVertexFourWidth 0 k : Real) * p i
  simpa [i] using (show Real.pi * (2 * (j : Real) + 1) <
    (sixVertexFourWidth 0 k : Real) * p i by nlinarith)

theorem sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j ∈
      Set.Ioo 0 Real.pi := by
  apply sixVertexEvenSymmetricLift_positive_mem_Ioo
  unfold sixVertexCanonicalDensityPerronPositiveHalfRoots
  rw [sixVertexEvenSymmetricLift_projection (k + 1)
    (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k).2.1]
  exact sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k

theorem sixVertexCanonicalDensityPerronPositiveHalfRoots_quantile_lower
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    Real.pi * (2 * (j : Real) + 1) <
      (sixVertexFourWidth 0 k : Real) *
        sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j := by
  exact sixVertexEvenPositiveHalfProjection_quantile_lower hc
    (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
    (sixVertexCanonicalDensityPerronBetheRoots_is_solution hc k) j


theorem sixVertexCanonicalDensityPerronBetheM_norm_ge
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    (c ^ 2 - 2) / 2 ≤
      ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ := by
  let q : Real := sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j
  let lower : Real := (c ^ 2 - 2) / 2
  let num : Real := (c ^ 2 - 1) ^ 2 + 1 +
    2 * (c ^ 2 - 1) * Real.cos q
  let den : Real := 2 - 2 * Real.cos q
  have hphase : sixVertexBethePhase q ≠ 1 := by
    exact SixVertexOpenRootSimplex.phase_ne_one_of_even
      (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
      (Fin.natAdd (k + 1) j)
  have hformula := sixVertexBetheM_phase_normSq c q hphase
  have hMne := sixVertexBetheM_phase_ne_zero hc q
  have hratioPos : 0 < num / den := by
    rw [← hformula]
    exact Complex.normSq_pos.mpr hMne
  have hden : 0 < den := by
    rcases (div_pos_iff.mp hratioPos) with h | h
    · exact h.2
    · have hnumNonneg : 0 ≤ num := by
        dsimp [num]
        have hcos := Real.neg_one_le_cos q
        have ha : 0 ≤ c ^ 2 - 1 := by nlinarith
        nlinarith [sq_nonneg (c ^ 2 - 2)]
      linarith
  have hdenLe : den ≤ 4 := by
    dsimp [den]
    linarith [Real.neg_one_le_cos q]
  have hlower : 0 < lower := by dsimp [lower]; nlinarith
  have hnum : (c ^ 2 - 2) ^ 2 ≤ num := by
    dsimp [num]
    have hcos := Real.neg_one_le_cos q
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcos ha.le]
  have hratio : lower ^ 2 ≤ num / den := by
    calc
      lower ^ 2 = (c ^ 2 - 2) ^ 2 / 4 := by dsimp [lower]; ring
      _ ≤ (c ^ 2 - 2) ^ 2 / den :=
        div_le_div_of_nonneg_left (sq_nonneg _) hden hdenLe
      _ ≤ num / den := div_le_div_of_nonneg_right hnum hden.le
  rw [← hformula, Complex.normSq_eq_norm_sq] at hratio
  change lower ≤ ‖sixVertexBetheM c (sixVertexBethePhase q)‖
  nlinarith [norm_nonneg (sixVertexBetheM c (sixVertexBethePhase q))]


theorem sixVertexCanonicalDensityPerronBetheM_norm_le_quantile
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ ≤
      c ^ 2 * (sixVertexFourWidth 0 k : Real) /
        (2 * (2 * (j : Real) + 1)) := by
  let p := sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j
  let N : Real := sixVertexFourWidth 0 k
  let s : Real := 2 * (j : Real) + 1
  let num : Real := (c ^ 2 - 1) ^ 2 + 1 +
    2 * (c ^ 2 - 1) * Real.cos p
  let den : Real := 2 - 2 * Real.cos p
  have hp := (sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo
    hc k j).1
  have hpPi := (sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo
    hc k j).2
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hs : 0 < s := by dsimp [s]; positivity
  have hphase : sixVertexBethePhase p ≠ 1 := by
    exact SixVertexOpenRootSimplex.phase_ne_one_of_even
      (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
      (Fin.natAdd (k + 1) j)
  have hformula := sixVertexBetheM_phase_normSq c p hphase
  have hMne := sixVertexBetheM_phase_ne_zero hc p
  have hratioPos : 0 < num / den := by
    rw [← hformula]
    exact Complex.normSq_pos.mpr hMne
  have hden : 0 < den := by
    rcases (div_pos_iff.mp hratioPos) with h | h
    · exact h.2
    · have hnumNonneg : 0 ≤ num := by
        dsimp [num]
        have hcos := Real.neg_one_le_cos p
        have ha : 0 ≤ c ^ 2 - 1 := by nlinarith
        nlinarith [sq_nonneg (c ^ 2 - 2)]
      linarith
  have hnum : num ≤ c ^ 4 := by
    dsimp [num]
    have hcos := Real.cos_le_one p
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcos ha.le]
  have habsp : |p| ≤ Real.pi := by
    rw [abs_of_pos hp]
    exact hpPi.le
  have hcos := Real.cos_le_one_sub_mul_cos_sq habsp
  have hdenP : 4 * p ^ 2 ≤ Real.pi ^ 2 * den := by
    have hcos' := mul_le_mul_of_nonneg_left hcos (sq_nonneg Real.pi)
    field_simp [Real.pi_ne_zero] at hcos'
    dsimp [den]
    nlinarith
  have hquant :=
    sixVertexCanonicalDensityPerronPositiveHalfRoots_quantile_lower hc k j
  change Real.pi * s < N * p at hquant
  have hquantSq : Real.pi ^ 2 * s ^ 2 ≤ N ^ 2 * p ^ 2 := by
    have hleft : 0 ≤ Real.pi * s := by positivity
    have hright : 0 ≤ N * p := by positivity
    nlinarith [(sq_le_sq₀ hleft hright).2 hquant.le]
  have hdenQuant : 4 * s ^ 2 ≤ N ^ 2 * den := by
    have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have hNnonneg : 0 ≤ N ^ 2 := sq_nonneg N
    have hs1 := mul_le_mul_of_nonneg_left hdenP hNnonneg
    have hs2 := mul_le_mul_of_nonneg_left hquantSq
      (by norm_num : (0 : Real) ≤ 4)
    nlinarith
  have hratio : num / den ≤ (c ^ 2 * N / (2 * s)) ^ 2 := by
    rw [div_le_iff₀ hden]
    have hc4 : 0 ≤ c ^ 4 := by positivity
    have hscale := mul_le_mul_of_nonneg_left hdenQuant hc4
    have hsne : s ≠ 0 := hs.ne'
    have hNne : N ≠ 0 := hN.ne'
    calc
      num ≤ c ^ 4 := hnum
      _ ≤ (c ^ 2 * N / (2 * s)) ^ 2 * den := by
        field_simp [hsne, hNne] at hscale ⊢
        nlinarith
  rw [← hformula, Complex.normSq_eq_norm_sq] at hratio
  change ‖sixVertexBetheM c (sixVertexBethePhase p)‖ ≤
    c ^ 2 * N / (2 * s)
  have hright : 0 ≤ c ^ 2 * N / (2 * s) := by positivity
  nlinarith [norm_nonneg (sixVertexBetheM c (sixVertexBethePhase p))]

theorem sixVertexCanonicalDensityPerronBetheM_log_norm_le_quantile
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    Real.log ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ ≤
      Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
        (2 * (2 * (j : Real) + 1))) := by
  have hleft : 0 < ‖sixVertexBetheM c (sixVertexBethePhase
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ :=
    norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _)
  exact Real.log_le_log hleft
    (sixVertexCanonicalDensityPerronBetheM_norm_le_quantile hc k j)


end
end StatMech.FrontierD
