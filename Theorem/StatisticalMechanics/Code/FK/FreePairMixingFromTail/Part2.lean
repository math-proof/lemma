/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePairMixingFromTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
import Theorem.StatisticalMechanics.Code.FK.FKTwoBoxDecoupling.Part2
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffErgodic
import Def.StatisticalMechanics.Code.FK.FreePairMixingFromTail.Part2
open MeasureTheory Set Filter Function
open scoped BigOperators ENNReal Topology


namespace StatMech

namespace FK

open ConfigSpace Lattice

variable {d : ℕ}


theorem mem_freeAxisVertexSupport_of_mem
    {F : Finset (Sym2 (Site d))} {e : Sym2 (Site d)} (he : e ∈ F)
    {x : Site d} (hx : x ∈ e) : x ∈ freeAxisVertexSupport F := by
  rw [freeAxisVertexSupport, Finset.mem_biUnion]
  refine ⟨e, he, ?_⟩
  have hout : s(e.out.1, e.out.2) = e := e.out_eq
  have hx' : x ∈ s(e.out.1, e.out.2) := by
    rw [hout]
    exact hx
  simpa only [Finset.mem_insert, Finset.mem_singleton] using
    (Sym2.mem_iff.mp hx')


theorem freeAxisTranslationPower_escape (hd : 1 ≤ d)
    (F : Finset (Sym2 (Site d))) (k : ℕ) :
    ∃ n : ℕ,
      (↑(F.image (fun e => (freeAxisTranslationPower hd n)⁻¹ • e)) :
          Set (Sym2 (Site d))) ⊆ (fkTailEdgeWindow d k)ᶜ := by
  let V := freeAxisVertexSupport F
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ x ∈ V, (x ⟨0, hd⟩).natAbs ≤ M :=
    ⟨V.sup fun x => (x ⟨0, hd⟩).natAbs,
      fun x hx => Finset.le_sup (f := fun x => (x ⟨0, hd⟩).natAbs) hx⟩
  refine ⟨M + k + 1, ?_⟩
  intro z hz
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
  obtain ⟨e, he, rfl⟩ := hz
  rw [Set.mem_compl_iff]
  intro hwindow
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxV : x ∈ V :=
        mem_freeAxisVertexSupport_of_mem he (Sym2.mem_mk_left x y)
      have hxBound : x ⟨0, hd⟩ ≤ (M : ℤ) := by
        have hnat := hM x hxV
        have habs := Int.le_natAbs (a := x ⟨0, hd⟩)
        omega
      have hxval :
          ((freeAxisTranslationPower hd (M + k + 1))⁻¹ • x) ⟨0, hd⟩ =
            x ⟨0, hd⟩ - (M + k + 1 : ℤ) := by
        change (-(Multiplicative.toAdd
          (freeAxisTranslationPower hd (M + k + 1))) + x) ⟨0, hd⟩ = _
        simp [freeAxisTranslationPower]
        ring
      have hxOutside :
          (freeAxisTranslationPower hd (M + k + 1))⁻¹ • x ∉ box d k := by
        rw [box, Set.mem_setOf_eq]
        intro hall
        have hcoord := hall ⟨0, hd⟩
        rw [hxval] at hcoord
        have hneg : x ⟨0, hd⟩ - (M + k + 1 : ℤ) ≤ -(k + 1 : ℤ) := by
          omega
        have hcast :
            ((x ⟨0, hd⟩ - (M + k + 1 : ℤ)).natAbs : ℤ) =
              -(x ⟨0, hd⟩ - (M + k + 1 : ℤ)) := by
          rw [← Int.natAbs_neg, Int.natAbs_of_nonneg]
          omega
        have hcoord' :
            ((x ⟨0, hd⟩ - (M + k + 1 : ℤ)).natAbs : ℤ) ≤ k := by
          exact_mod_cast hcoord
        rw [hcast] at hcoord'
        omega
      apply hxOutside
      apply hwindow ((freeAxisTranslationPower hd (M + k + 1))⁻¹ • x)
      rw [Percolation.smul_sym2_mk]
      exact Sym2.mem_mk_left _ _


theorem freeInfiniteVolume_axisShift_ergodic
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    _root_.Ergodic
      (shift (freeAxisTranslation hd) :
        ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) := by
  let mu := (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) :
    Measure (ConfigSpace (Sym2 (Site d))))
  have hti : IsTranslationInvariant (G := Multiplicative (Site d)) mu :=
    bdp_freeIV_isTranslationInvariant hp hp1
  refine ⟨hti (freeAxisTranslation hd), ⟨?_⟩⟩
  intro s hs hinv
  have hinvPow : ∀ n : ℕ,
      shift (freeAxisTranslationPower hd n) ⁻¹' s = s := by
    intro n
    rw [shift_freeAxisTranslationPower]
    exact Function.IsFixedPt.preimage_iterate hinv n
  obtain ⟨t, ht, hae⟩ :=
    ati_sequenceInvariant_aeTail (fkTailEdgeWindow d)
      fkTailEdgeWindow_mono (freeAxisTranslationPower hd)
      (freeAxisTranslationPower_escape hd) hti s hs hinvPow
  rw [eventuallyConst_set']
  rcases freeInfiniteVolume_tail_trivial hp hp1 t ht with ht0 | ht1
  · exact Or.inl (hae.trans (ae_eq_empty.mpr ht0))
  · right
    apply hae.trans
    rw [ae_eq_univ]
    rw [measure_compl ht.measurableSet (measure_ne_top mu t), ht1,
      measure_univ]
    simp

theorem free_moInd_mem_Icc (T : Finset (Sym2 (Site d)))
    (omega : ConfigSpace (Sym2 (Site d))) :
    fmu_moInd T omega ∈ Set.Icc (0 : ℝ) 1 := by
  rw [fmu_moInd_eq_indicator]
  by_cases h : omega ∈ fmu_multiOpen T <;> simp [h]

theorem free_birkhoffAverage_moInd_mem_Icc
    (Tmap : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
    (T : Finset (Sym2 (Site d))) (n : ℕ)
    (omega : ConfigSpace (Sym2 (Site d))) :
    birkhoffAverage ℝ Tmap (fmu_moInd T) n omega ∈ Set.Icc (0 : ℝ) 1 := by
  rcases n with _ | n
  · simp [birkhoffAverage]
  · have hterm : ∀ k ∈ Finset.range (n + 1),
        fmu_moInd T (Tmap^[k] omega) ∈ Set.Icc (0 : ℝ) 1 :=
      fun k _ => free_moInd_mem_Icc T _
    have hsum0 : 0 ≤ ∑ k ∈ Finset.range (n + 1),
        fmu_moInd T (Tmap^[k] omega) :=
      Finset.sum_nonneg fun k hk => (hterm k hk).1
    have hsum1 : (∑ k ∈ Finset.range (n + 1),
        fmu_moInd T (Tmap^[k] omega)) ≤ (n + 1 : ℝ) := by
      calc
        (∑ k ∈ Finset.range (n + 1),
            fmu_moInd T (Tmap^[k] omega))
            ≤ ∑ _k ∈ Finset.range (n + 1), (1 : ℝ) :=
              Finset.sum_le_sum fun k hk => (hterm k hk).2
        _ = (n + 1 : ℝ) := by simp
    simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
    norm_num [Nat.cast_add, Nat.cast_one] at hsum1 ⊢
    constructor
    · exact mul_nonneg (inv_nonneg.mpr (by positivity)) hsum0
    · calc
        (n + 1 : ℝ)⁻¹ *
            (∑ k ∈ Finset.range (n + 1), fmu_moInd T (Tmap^[k] omega))
            ≤ (n + 1 : ℝ)⁻¹ * (n + 1 : ℝ) :=
              mul_le_mul_of_nonneg_left hsum1 (inv_nonneg.mpr (by positivity))
        _ = 1 := inv_mul_cancel₀ (by positivity)

theorem freeAxis_integral_mul_birkhoffAverage
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (T U : Finset (Sym2 (Site d))) (n : ℕ) :
    let mu := (freeInfiniteVolume d hp hp1
      (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
    ∫ omega, fmu_moInd T omega *
        birkhoffAverage ℝ (shift (freeAxisTranslation hd))
          (fmu_moInd U) n omega ∂mu =
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        mu.real (fmu_multiOpen T ∩
          shift (freeAxisTranslationPower hd k) ⁻¹' fmu_multiOpen U) := by
  dsimp only
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
  have hpoint : (fun omega => fmu_moInd T omega *
      birkhoffAverage ℝ (shift (freeAxisTranslation hd))
        (fmu_moInd U) n omega) =
      fun omega => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        fmu_moInd T omega *
          fmu_moInd U (shift (freeAxisTranslationPower hd k) omega) := by
    funext omega
    simp only [birkhoffAverage, birkhoffSum, smul_eq_mul,
      shift_freeAxisTranslationPower]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hpoint, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [fmu_moInd_mul_shift_eq,
      MeasureTheory.integral_indicator_const (1 : ℝ)]
    · simp
    · exact (fmu_multiOpen_measurable T).inter
        ((fmu_multiOpen_measurable U).preimage
          (measurable_shift (freeAxisTranslationPower hd k)))
  · intro k hk
    exact fmu_integrable_moInd_mul_shift
      (μ := mu) (freeAxisTranslationPower hd k) T U


theorem freeInfiniteVolume_pairCorrelationAverage_tendsto
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (T U : Finset (Sym2 (Site d))) :
    let mu := (freeInfiniteVolume d hp hp1
      (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        mu.real (fmu_multiOpen T ∩
          shift (freeAxisTranslationPower hd k) ⁻¹' fmu_multiOpen U))
      atTop (𝓝 (mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U))) := by
  dsimp only
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
  let Tmap := (shift (freeAxisTranslation hd) :
    ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
  have herg : _root_.Ergodic Tmap mu :=
    freeInfiniteVolume_axisShift_ergodic hd hp hp1
  have hbirk := StatMech.BirkhoffAE.Ergodic.tendsto_birkhoffAverage_integral_ae
    herg (fmu_integrable_moInd (μ := mu) U)
  let F : ℕ → ConfigSpace (Sym2 (Site d)) → ℝ := fun n omega =>
    fmu_moInd T omega * birkhoffAverage ℝ Tmap (fmu_moInd U) n omega
  have hlim : ∀ᵐ omega ∂mu, Tendsto (fun n => F n omega) atTop
      (𝓝 (fmu_moInd T omega * mu.real (fmu_multiOpen U))) := by
    filter_upwards [hbirk] with omega homega
    have hmass : (∫ x, fmu_moInd U x ∂mu) =
        mu.real (fmu_multiOpen U) := fmu_integral_moInd U
    rw [hmass] at homega
    exact tendsto_const_nhds.mul homega
  have hmeas : ∀ n, AEStronglyMeasurable (F n) mu := by
    intro n
    exact MeasureTheory.AEStronglyMeasurable.mul
      (fmu_integrable_moInd (μ := mu) T).aestronglyMeasurable
      (StatMech.BirkhoffAE.aestronglyMeasurable_birkhoffAverage
        herg.toMeasurePreserving (fmu_integrable_moInd (μ := mu) U) n)
  have hbound : ∀ n, ∀ᵐ omega ∂mu, ‖F n omega‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards with omega
    have hT := free_moInd_mem_Icc T omega
    have hU := free_birkhoffAverage_moInd_mem_Icc Tmap U n omega
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hT.1 hU.1)]
    exact mul_le_one₀ hT.2 hU.1 hU.2
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := mu) (fun _ => (1 : ℝ)) hmeas (by fun_prop) hbound hlim
  have hlimitIntegral :
      (∫ omega, fmu_moInd T omega * mu.real (fmu_multiOpen U) ∂mu) =
        mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U) := by
    rw [MeasureTheory.integral_mul_const, fmu_integral_moInd]
  rw [hlimitIntegral] at hdct
  simpa only [F, Tmap, mu, freeAxis_integral_mul_birkhoffAverage hd hp hp1 T U]
    using hdct

end FK
end StatMech
