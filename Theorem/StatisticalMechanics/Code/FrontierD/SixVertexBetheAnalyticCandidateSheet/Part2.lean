/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticStabilitySheet
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSymmetricBetheEigenvalueKernel_eq_value
    {m : Nat} (c : Real) (q : Fin m → Real)
    (hq : ∀ j, q j ∈ Set.Ioo 0 Real.pi) :
    sixVertexSymmetricBetheEigenvalueKernel c q =
      sixVertexSymmetricBetheEigenvalueValue c q := by
  unfold sixVertexSymmetricBetheEigenvalueKernel
    sixVertexSymmetricBetheEigenvalueValue
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq]
  exact (sixVertexBetheM_phase_normSq c (q j)
    (sixVertexBethePhase_ne_one_of_mem_Ioo
      ⟨(neg_lt_zero.mpr Real.pi_pos).trans (hq j).1, (hq j).2⟩
      (ne_of_gt (hq j).1))).symm


theorem analyticOnNhd_sixVertexSymmetricBetheEigenvalueKernel
    {m : Nat} {U : Set Real} (q : Real → Fin m → Real)
    (hqAnalytic : AnalyticOnNhd Real q U)
    (hq : ∀ c ∈ U, ∀ j, q c j ∈ Set.Ioo 0 Real.pi) :
    AnalyticOnNhd Real
      (fun c => sixVertexSymmetricBetheEigenvalueKernel c (q c)) U := by
  intro c hc
  have hcoord (j : Fin m) : AnalyticAt Real (fun t => q t j) c :=
    by
      simpa only [Function.comp_apply] using
        ((ContinuousLinearMap.proj (R := Real) j).analyticAt (q c)).comp
          (hqAnalytic c hc)
  have hden (j : Fin m) : 2 - 2 * Real.cos (q c j) ≠ 0 := by
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
      (show (0 : Real) ≤ 0 by rfl) (hq c hc j).2.le (hq c hc j).1
    rw [Real.cos_zero] at hcos
    nlinarith
  unfold sixVertexSymmetricBetheEigenvalueKernel
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod Finset.univ
  intro j _
  apply AnalyticAt.div
  · fun_prop
  · fun_prop
  · exact hden j

theorem sixVertexEvenSymmetricLift_positive_mem_Ioo
    {m : Nat} {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (j : Fin m) : q j ∈ Set.Ioo 0 Real.pi := by
  have hnonneg := (sixVertexEvenSymmetricLift_positive_mem_Icc hopen j).1
  have hpos : 0 < q j := hnonneg.lt_of_ne (fun h => by
    let i : Fin (m + m) := Fin.natAdd m j
    let ir : Fin (m + m) := Fin.castAdd m j.rev
    have hi : sixVertexEvenSymmetricLift m q i = 0 := by
      change sixVertexEvenSymmetricLift m q (Fin.natAdd m j) = 0
      rw [sixVertexEvenSymmetricLift_natAdd]
      exact h.symm
    have hir : sixVertexEvenSymmetricLift m q ir = 0 := by
      change sixVertexEvenSymmetricLift m q (Fin.castAdd m j.rev) = 0
      rw [sixVertexEvenSymmetricLift_castAdd]
      simp only [Fin.rev_rev]
      linarith
    have hieq : i = ir := hopen.1.injective (hi.trans hir.symm)
    have hval := congrArg Fin.val hieq
    simp [i, ir, Fin.castAdd, Fin.rev] at hval
    omega)
  have hpi := (hopen.2.2 (Fin.natAdd m j)).2
  rw [sixVertexEvenSymmetricLift_natAdd] at hpi
  exact ⟨hpos, hpi⟩

theorem sixVertexEvenSymmetricLift_ne_zero
    {m : Nat} {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (i : Fin (m + m)) : sixVertexEvenSymmetricLift m q i ≠ 0 := by
  intro hi
  have hir : sixVertexEvenSymmetricLift m q i.rev = 0 := by
    have hs := hopen.2.1 i
    rw [hi, neg_zero] at hs
    exact hs
  have hieq : i = i.rev := hopen.1.injective (hi.trans hir.symm)
  have hval := congrArg Fin.val hieq
  simp [Fin.rev] at hval
  omega


theorem sixVertexAnalyticEvenSymmetricBetheCandidate_eqOn_top
    {N m : Nat} (hm : 0 < m) (hn : m + m ≤ N)
    {U : Set Real} (hU : IsPreconnected U) (hUopen : IsOpen U)
    (hUtwo : U ⊆ Set.Ioi 2)
    (roots : C(Real, Fin (m + m) → Real))
    (hopen : ∀ t ∈ U, SixVertexOpenRootSimplex (roots t))
    (hsol : ∀ t ∈ U,
      SixVertexSatisfiesBetheEquations t N (m + m) (roots t))
    (hrootAnalytic : AnalyticOnNhd Real roots U)
    {c₀ : Real} (hc₀U : c₀ ∈ U)
    (hwave : sixVertexCoordinateBetheWave (N := N) c₀ (roots c₀) ≠ 0)
    (hbase : sixVertexSymmetricBetheEigenvalueKernel c₀
        (sixVertexEvenPositiveHalfProjection m (roots c₀)) =
      sixVertexSectorTopEigenvalue N (m + m) hn c₀) :
    Set.EqOn
      (fun t => sixVertexSymmetricBetheEigenvalueKernel t
        (sixVertexEvenPositiveHalfProjection m (roots t)))
      (sixVertexSectorTopEigenvalue N (m + m) hn) U := by
  let q : Real → Fin m → Real := fun t =>
    sixVertexEvenPositiveHalfProjection m (roots t)
  let f : Real → Real := fun t =>
    sixVertexSymmetricBetheEigenvalueKernel t (q t)
  have hqAnalytic : AnalyticOnNhd Real q U := by
    intro t ht
    simpa only [q, Function.comp_apply] using
      ((sixVertexEvenPositiveHalfProjection m).analyticAt (roots t)).comp
        (hrootAnalytic t ht)
  have hqpos : ∀ t ∈ U, ∀ j, q t j ∈ Set.Ioo 0 Real.pi := by
    intro t ht j
    have hlift : sixVertexEvenSymmetricLift m (q t) = roots t :=
      sixVertexEvenSymmetricLift_projection m (hopen t ht).2.1
    apply sixVertexEvenSymmetricLift_positive_mem_Ioo
    rw [hlift]
    exact hopen t ht
  have hfAnalytic : AnalyticOnNhd Real f U := by
    exact analyticOnNhd_sixVertexSymmetricBetheEigenvalueKernel
      q hqAnalytic hqpos
  have heigen : ∀ t ∈ U,
      SixVertexCoordinateBetheEigenrelation (N := N) t (roots t) := by
    intro t ht
    have hphase : ∀ i, sixVertexBethePhase (roots t i) ≠ 1 := by
      intro i
      let qt := q t
      have hlift : sixVertexEvenSymmetricLift m qt = roots t :=
        sixVertexEvenSymmetricLift_projection m (hopen t ht).2.1
      apply sixVertexBethePhase_ne_one_of_mem_Ioo ((hopen t ht).2.2 i)
      rw [← hlift]
      exact sixVertexEvenSymmetricLift_ne_zero (by rw [hlift]; exact hopen t ht) i
    exact (hsol t ht).multiplicative
      |>.physicalCoordinateBetheEigenrelation_of_pos
        (hUtwo ht) (by omega) (roots t) hphase
  have hcandidate : ∀ t ∈ U,
      sixVertexBetheEigenvalueCandidate t (roots t) = (f t : Complex) := by
    intro t ht
    have hlift : sixVertexEvenSymmetricLift m (q t) = roots t :=
      sixVertexEvenSymmetricLift_projection m (hopen t ht).2.1
    rw [← hlift,
      sixVertexBetheEigenvalueCandidate_evenSymmetricLift_eq_value]
    exact_mod_cast (sixVertexSymmetricBetheEigenvalueKernel_eq_value
      t (q t) (hqpos t ht)).symm
  have hwaveContinuous : ContinuousAt
      (fun t => sixVertexCoordinateBetheWave (N := N) t (roots t)) c₀ :=
    (continuous_sixVertexCoordinateBetheWave_branch roots roots.continuous).continuousAt
  have hUzero : U ⊆ Set.Ioi 0 := by
    intro t ht
    have httwo := hUtwo ht
    change 2 < t at httwo
    change 0 < t
    linarith
  have hc₀pos : 0 < c₀ := hUzero hc₀U
  apply sixVertexBetheCandidate_eqOn_top_of_analyticSheet_of_nonzero_at
    hn hU hUopen hUzero hc₀U hc₀pos roots f hfAnalytic heigen hcandidate
      hwaveContinuous hwave
  exact hbase


theorem eventually_sixVertexHalfFilledBetheCandidate_eq_top_and_wave_ne_zero
    (k : Nat) :
    ∀ᶠ c : Real in atTop, ∀ hc : 2 < c,
      sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexPositiveHalfBetheRoots hc k) =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega) c ∧
      sixVertexCoordinateBetheWave (N := sixVertexFourWidth 0 k) c
        (sixVertexHalfFilledBetheRoots hc k) ≠ 0 := by
  filter_upwards
    [eventually_sixVertexHalfFilledBetheCandidate_eq_top_vandermonde k,
      eventually_exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero k]
      with c hcandidate hrotated
  intro hc
  refine ⟨hcandidate hc, ?_⟩
  obtain ⟨a, ha⟩ := hrotated hc
  intro hwave
  apply ha
  funext x
  unfold sixVertexHalfFilledBetheRotatedRealWave
  rw [show sixVertexCoordinateBetheWave c
      (sixVertexHalfFilledBetheRoots hc k) x = 0 by
    exact congrFun hwave x]
  simp


end
end StatMech.FrontierD
