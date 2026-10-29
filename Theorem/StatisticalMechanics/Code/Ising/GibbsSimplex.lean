/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Ising.DLR
import Def.StatisticalMechanics.Code.Ising.GibbsSimplex
open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped BigOperators ENNReal

set_option linter.style.longLine false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


theorem measurableSet_mem_finInterSystem {Ω : Type*} [MeasurableSpace Ω]
    {S : Set (Set Ω)} (hSm : ∀ s ∈ S, MeasurableSet s) {t : Set Ω}
    (ht : t ∈ finInterSystem S) : MeasurableSet t := by
  obtain ⟨F, rfl⟩ := ht
  exact MeasurableSet.sInter (F.countable_toSet.image _)
    (by rintro u ⟨v, _, rfl⟩; exact hSm v.1 v.2)

theorem isPiSystem_finInterSystem {Ω : Type*} (S : Set (Set Ω)) :
    IsPiSystem (finInterSystem S) := by
  rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩ _
  exact ⟨F ∪ G, by simp only [Finset.coe_union, Set.image_union, Set.sInter_union]⟩

theorem generateFrom_finInterSystem {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {S : Set (Set Ω)} (hgen : MeasurableSpace.generateFrom S = mΩ) :
    MeasurableSpace.generateFrom (finInterSystem S) = mΩ := by
  apply le_antisymm
  · rw [← hgen]; apply generateFrom_le
    intro t ht; obtain ⟨F, rfl⟩ := ht
    apply MeasurableSet.sInter (F.countable_toSet.image _)
    rintro u ⟨v, _, rfl⟩; exact measurableSet_generateFrom v.2
  · rw [← hgen]; apply generateFrom_mono
    intro s hs; exact ⟨{⟨s, hs⟩}, by simp⟩


theorem kernel_ae_eq_trim {Ω : Type*}
    (mΩ : MeasurableSpace Ω) [hcg : @CountablyGenerated Ω mΩ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (k₁ k₂ : @Kernel Ω Ω m mΩ)
    (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    (hp1 : ∀ η, @IsProbabilityMeasure Ω mΩ (k₁ η))
    (hp2 : ∀ η, @IsProbabilityMeasure Ω mΩ (k₂ η))
    (h : k₁ =ᵐ[μ] k₂) :
    k₁ =ᵐ[μ.trim hm] k₂ := by
  set S := @countableGeneratingSet Ω mΩ hcg with hS
  set C := @finInterSystem Ω S with hC
  have hCcount : C.Countable := by
    have : Countable S := (@countable_countableGeneratingSet Ω mΩ hcg).to_subtype
    exact Set.countable_range _
  have hSm : ∀ s ∈ S, @MeasurableSet Ω mΩ s :=
    fun s hs => @measurableSet_countableGeneratingSet Ω mΩ hcg s hs
  have hCm : ∀ t ∈ C, @MeasurableSet Ω mΩ t := fun t ht =>
    @measurableSet_mem_finInterSystem Ω mΩ S hSm t ht
  have hgenC : @MeasurableSpace.generateFrom Ω C = mΩ :=
    @generateFrom_finInterSystem Ω mΩ S (@generateFrom_countableGeneratingSet Ω mΩ hcg)
  have hpiC : IsPiSystem C := @isPiSystem_finInterSystem Ω S
  have hper : ∀ t ∈ C, (fun η => k₁ η t) =ᵐ[μ.trim hm] (fun η => k₂ η t) := by
    intro t ht
    have hμae : (fun η => k₁ η t) =ᵐ[μ] (fun η => k₂ η t) := by
      filter_upwards [h] with η hη; rw [hη]
    exact ae_eq_trim_of_measurable hm (k₁.measurable_coe (hCm t ht))
      (k₂.measurable_coe (hCm t ht)) hμae
  have hall : ∀ᵐ η ∂(μ.trim hm), ∀ t ∈ C, k₁ η t = k₂ η t := by
    rw [ae_ball_iff hCcount]; exact hper
  filter_upwards [hall] with η hη
  haveI h1 : @IsProbabilityMeasure Ω mΩ (k₁ η) := hp1 η
  haveI h2 : @IsProbabilityMeasure Ω mΩ (k₂ η) := hp2 η
  refine @ext_of_generate_finite Ω mΩ (k₁ η) (k₂ η) C hgenC.symm hpiC inferInstance
    (fun t ht => hη t ht) ?_
  rw [h1.measure_univ, h2.measure_univ]


theorem trim_smul {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    (μ : @Measure Ω mΩ) (hm : m ≤ mΩ) (a : ENNReal) :
    (a • μ).trim hm = a • (μ.trim hm) :=
  @Measure.ext _ m _ _ (fun s hs => by
    rw [Measure.smul_apply, trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs,
      Measure.smul_apply])


theorem meas_glue (n : ℕ) (τ : {x // x ∈ box d n} → Bool) :
    Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => glue η τ) := by
  refine (@measurable_pi_iff (ConfigSpace (Site d)) (Site d) (fun _ => Bool)
    (outsideSigma (box d n)) _ (fun η => glue η τ)).mpr ?_
  intro x
  by_cases hx : x ∈ box d n
  · simp only [glue, hx, dif_pos]; exact measurable_const
  · simp only [glue, hx, dif_neg, not_false_iff]
    have hmem : x ∈ (box d n)ᶜ := hx
    have hle : MeasurableSpace.comap (ConfigSpace.eval x) inferInstance ≤ outsideSigma (box d n) :=
      le_iSup₂ (f := fun e (_ : e ∈ (box d n)ᶜ) =>
        MeasurableSpace.comap (ConfigSpace.eval e) inferInstance) x hmem
    exact Measurable.mono (measurable_iff_comap_le.mpr le_rfl) hle le_rfl

theorem meas_glue_eval (n : ℕ) (τ : {x // x ∈ box d n} → Bool) (x : Site d) :
    Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => (glue η τ) x) :=
  (measurable_pi_apply x).comp (meas_glue n τ)

theorem meas_spin_glue (n : ℕ) (τ : {x // x ∈ box d n} → Bool) (x : Site d) :
    Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => spin (glue η τ) x) :=
  (measurable_from_top (f := fun b : Bool => if b then (1 : ℝ) else -1)).comp
    (meas_glue_eval n τ x)

theorem meas_bond_glue (n : ℕ) (τ : {x // x ∈ box d n} → Bool) (e : Sym2 (Site d)) :
    Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => bond (glue η τ) e) := by
  induction e using Sym2.inductionOn with
  | hf x y => simp only [bond_mk]; exact (meas_spin_glue n τ x).mul (meas_spin_glue n τ y)

theorem meas_fvEnergy (n : ℕ) (B : Finset (Sym2 (Site d))) (h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => fvEnergy η n B h τ) := by
  unfold fvEnergy
  refine Measurable.sub (Measurable.neg (Finset.measurable_sum _ ?_))
    (Measurable.const_mul (Finset.measurable_sum _ ?_) _)
  · intro e _; exact meas_bond_glue n τ e
  · intro x _; exact meas_spin_glue n τ x

theorem meas_fvWeight (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => fvWeight η n B β h τ) := by
  unfold fvWeight
  exact Real.measurable_exp.comp ((meas_fvEnergy n B h τ).const_mul _)

theorem meas_fvZ (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => fvZ η n B β h) := by
  unfold fvZ
  exact Finset.measurable_sum _ (fun τ _ => meas_fvWeight n B β h τ)

theorem meas_fvProb (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => fvProb η n B β h τ) := by
  unfold fvProb
  exact (meas_fvWeight n B β h τ).div (meas_fvZ n B β h)

theorem meas_dirac_glue (n : ℕ) (τ : {x // x ∈ box d n} → Bool)
    {s : Set (ConfigSpace (Site d))} (hs : MeasurableSet s) :
    Measurable[outsideSigma (box d n)]
      (fun η : ConfigSpace (Site d) => (Measure.dirac (glue η τ)) s) :=
  (Measure.measurable_coe hs).comp (Measure.measurable_dirac.comp (meas_glue n τ))

theorem meas_fvMeasure_coe (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    {s : Set (ConfigSpace (Site d))} (hs : MeasurableSet s) :
    Measurable[outsideSigma (box d n)]
      (fun η : ConfigSpace (Site d) => (fvMeasure η n B β h) s) := by
  have heq : (fun η : ConfigSpace (Site d) => (fvMeasure η n B β h) s)
      = (fun η => ∑ τ : {x // x ∈ box d n} → Bool,
          ENNReal.ofReal (fvProb η n B β h τ) * (Measure.dirac (glue η τ)) s) := by
    funext η
    unfold fvMeasure
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
  rw [heq]
  refine Finset.measurable_sum _ (fun τ _ => ?_)
  exact (ENNReal.measurable_ofReal.comp (meas_fvProb n B β h τ)).mul (meas_dirac_glue n τ hs)


end Ising
end StatMech
