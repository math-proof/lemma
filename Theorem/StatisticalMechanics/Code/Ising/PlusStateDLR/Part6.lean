/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Def.StatisticalMechanics.Code.Ising.PlusStateDLR.Part5
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


theorem outsideSigma_le_invariant {E : Type*} [Countable E] (Λ : Set E) :
    outsideSigma Λ ≤ outsideInvariantMS Λ := by
  refine iSup₂_le (fun e he => ?_)
  
  rintro s ⟨t, _, rfl⟩ ω ω' hagree
  have : ω e = ω' e := hagree e he
  simp only [Set.mem_preimage, ConfigSpace.eval]
  rw [this]


theorem glue_mem_iff_of_outsideSigma (n : ℕ) {s : Set (ConfigSpace (Site d))}
    (hs : MeasurableSet[outsideSigma (box d n)] s) (ω : ConfigSpace (Site d))
    (τ : {x // x ∈ box d n} → Bool) :
    glue ω τ ∈ s ↔ ω ∈ s :=
  (outsideSigma_le_invariant (box d n) s hs) (glue ω τ) ω
    (fun x hx => by rw [glue_not_mem ω τ hx])


theorem fvMeasure_apply_eq_sum (ω : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) {t : Set (ConfigSpace (Site d))}
    (ht : MeasurableSet t) :
    (fvMeasure ω n B β h) t
      = ∑ τ : {x // x ∈ box d n} → Bool,
          ENNReal.ofReal (fvProb ω n B β h τ) * (Set.indicator t (1 : ConfigSpace (Site d) → ENNReal) (glue ω τ)) := by
  unfold fvMeasure
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ ht]


theorem fvMeasure_inter_outsideSigma (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    {s : Set (ConfigSpace (Site d))} (hs : MeasurableSet[outsideSigma (box d n)] s)
    {t : Set (ConfigSpace (Site d))} (ht : MeasurableSet t) (ω : ConfigSpace (Site d)) :
    (fvMeasure ω n B β h) (s ∩ t)
      = (Set.indicator s (1 : ConfigSpace (Site d) → ENNReal) ω) * (fvMeasure ω n B β h) t := by
  have hst : MeasurableSet (s ∩ t) := ((outsideSigma_le (box d n)) s hs).inter ht
  rw [fvMeasure_apply_eq_sum ω n B β h hst, fvMeasure_apply_eq_sum ω n B β h ht,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  
  have hloc : glue ω τ ∈ s ↔ ω ∈ s := glue_mem_iff_of_outsideSigma n hs ω τ
  by_cases hωs : ω ∈ s
  · have hglue_s : glue ω τ ∈ s := hloc.mpr hωs
    rw [Set.indicator_of_mem hωs, Pi.one_apply, one_mul]
    congr 1
    by_cases hglue_t : glue ω τ ∈ t
    · rw [Set.indicator_of_mem (show glue ω τ ∈ s ∩ t from ⟨hglue_s, hglue_t⟩),
        Set.indicator_of_mem hglue_t]
    · rw [Set.indicator_of_notMem (show glue ω τ ∉ s ∩ t from fun hc => hglue_t hc.2),
        Set.indicator_of_notMem hglue_t]
  · have hglue_s : glue ω τ ∉ s := fun hc => hωs (hloc.mp hc)
    rw [Set.indicator_of_notMem hωs,
      Set.indicator_of_notMem (show glue ω τ ∉ s ∩ t from fun hc => hglue_s hc.1)]
    simp


theorem psdlr_compProd_rect (β h : ℝ) (hcons : FVConsistency d β h) (n : ℕ)
    {s : Set (ConfigSpace (Site d))} (hs : MeasurableSet[outsideSigma (box d n)] s)
    {t : Set (ConfigSpace (Site d))} (ht : MeasurableSet t) :
    (((plusState d β h : Measure (ConfigSpace (Site d))).trim (outsideSigma_le (box d n)))
        ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h)) (s ×ˢ t)
      = (plusState d β h : Measure (ConfigSpace (Site d))) (s ∩ t) := by
  set μ := (plusState d β h : Measure (ConfigSpace (Site d))) with hμ
  set hm := outsideSigma_le (box d n) with hmdef
  set B := bondFinsetTouch d n with hB
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  haveI : SigmaFinite (μ.trim hm) := by
    haveI : IsFiniteMeasure (μ.trim hm) := ⟨by
      rw [trim_measurableSet_eq hm MeasurableSet.univ]; exact measure_lt_top μ _⟩
    infer_instance
  
  rw [Measure.compProd_apply_prod hs ht]
  
  have hker : ∀ ω, (isingSpec n B β h) ω t = (fvMeasure ω n B β h) t :=
    fun ω => by rw [isingSpec_apply]
  simp_rw [hker]
  
  rw [setLIntegral_trim hm (meas_fvMeasure_coe n B β h ht) hs]
  
  have hsfull : MeasurableSet s := (outsideSigma_le (box d n)) s hs
  rw [← lintegral_indicator hsfull]
  have heq : (fun ω => Set.indicator s (fun ω => (fvMeasure ω n B β h) t) ω)
      = (fun ω => (fvMeasure ω n B β h) (s ∩ t)) := by
    funext ω
    by_cases hωs : ω ∈ s
    · rw [Set.indicator_of_mem hωs, fvMeasure_inter_outsideSigma n B β h hs ht ω,
        Set.indicator_of_mem hωs, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem hωs, fvMeasure_inter_outsideSigma n B β h hs ht ω,
        Set.indicator_of_notMem hωs]
      simp
  rw [heq]
  
  have hbindapp : (isingSpecFull n B β h ∘ₘ μ) (s ∩ t)
      = ∫⁻ ω, (fvMeasure ω n B β h) (s ∩ t) ∂μ := by
    rw [Measure.bind_apply (((outsideSigma_le (box d n)) s hs).inter ht)
      (isingSpecFull n B β h).aemeasurable]
    rfl
  rw [← hbindapp, psdlr_bind_eq β h hcons n]


theorem psdlr_compProd_trim_eq (β h : ℝ) (hcons : FVConsistency d β h) (n : ℕ) :
    ((plusState d β h : Measure (ConfigSpace (Site d))).trim (outsideSigma_le (box d n)))
        ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h)
      = @Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _
          ((outsideSigma (box d n)).prod inferInstance) (fun ω ↦ (id ω, id ω))
          (plusState d β h : Measure (ConfigSpace (Site d))) := by
  set μ := (plusState d β h : Measure (ConfigSpace (Site d))) with hμ
  set hm := outsideSigma_le (box d n) with hmdef
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  haveI : SigmaFinite (μ.trim hm) := by
    haveI : IsFiniteMeasure (μ.trim hm) := ⟨by
      rw [trim_measurableSet_eq hm MeasurableSet.univ]; exact measure_lt_top μ _⟩
    infer_instance
  set K := isingSpec n (bondFinsetTouch d n) β h with hK
  haveI : IsMarkovKernel K := isMarkov_isingSpec n (bondFinsetTouch d n) β h
  
  have hcs : IsCountablySpanning {s : Set (ConfigSpace (Site d)) | MeasurableSet[outsideSigma (box d n)] s} :=
    ⟨fun _ => Set.univ, fun _ => Set.mem_setOf.mpr MeasurableSet.univ, by rw [Set.iUnion_const]⟩
  have hcs0 : IsCountablySpanning {t : Set (ConfigSpace (Site d)) | MeasurableSet t} :=
    ⟨fun _ => Set.univ, fun _ => Set.mem_setOf.mpr MeasurableSet.univ, by rw [Set.iUnion_const]⟩
  have hgenC : ((outsideSigma (box d n)).prod inferInstance)
      = generateFrom (Set.image2 (fun a b : Set (ConfigSpace (Site d)) => a ×ˢ b)
          {s | MeasurableSet[outsideSigma (box d n)] s} {t | MeasurableSet t}) :=
    (@generateFrom_eq_prod (ConfigSpace (Site d)) (ConfigSpace (Site d))
      (outsideSigma (box d n)) inferInstance _ _
      (@generateFrom_measurableSet _ (outsideSigma (box d n))) (@generateFrom_measurableSet _ _)
      hcs hcs0).symm
  have hpiC : IsPiSystem (Set.image2 (fun a b : Set (ConfigSpace (Site d)) => a ×ˢ b)
      {s | MeasurableSet[outsideSigma (box d n)] s} {t | MeasurableSet t}) :=
    @isPiSystem_prod (ConfigSpace (Site d)) (ConfigSpace (Site d)) (outsideSigma (box d n)) _
  
  have hf : @Measurable (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d))
      inferInstance ((outsideSigma (box d n)).prod inferInstance) (fun ω => (id ω, id ω)) :=
    (measurable_id'' hm).prodMk measurable_id
  
  refine @Measure.ext_of_generateFrom_of_iUnion (ConfigSpace (Site d) × ConfigSpace (Site d))
    ((outsideSigma (box d n)).prod inferInstance) _ _ _ (fun _ => Set.univ) hgenC hpiC
    (by rw [Set.iUnion_const])
    (fun _ => Set.mem_image2.mpr
      ⟨Set.univ, Set.mem_setOf.mpr MeasurableSet.univ, Set.univ,
        Set.mem_setOf.mpr MeasurableSet.univ, by simp⟩)
    (fun _ => ?_) (fun r hr => ?_)
  · 
    exact (measure_lt_top ((μ.trim hm) ⊗ₘ K) _).ne
  · 
    rw [Set.mem_image2] at hr
    obtain ⟨s, hs, t, ht, rfl⟩ := hr
    simp only [Set.mem_setOf_eq] at hs ht
    
    have hLeft : ((μ.trim hm) ⊗ₘ K) (s ×ˢ t) = μ (s ∩ t) :=
      psdlr_compProd_rect β h hcons n hs ht
    
    have hRight : (@Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _
        ((outsideSigma (box d n)).prod inferInstance) (fun ω ↦ (id ω, id ω)) μ) (s ×ˢ t)
        = μ (s ∩ t) := by
      rw [Measure.map_apply (μ := μ) hf
        (@MeasurableSet.prod _ _ (outsideSigma (box d n)) _ s t hs ht)]
      rfl
    rw [hLeft, hRight]


theorem psdlr_plusState_isDLR (β h : ℝ) (hcons : FVConsistency d β h) :
    IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))) :=
  isDLRState_of_compProd_trim β h _ (fun n => psdlr_compProd_trim_eq β h hcons n)

end Ising
end StatMech
