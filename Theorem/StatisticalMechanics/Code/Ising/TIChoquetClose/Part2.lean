/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Ising.GibbsChoquet.Part2
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtremeClose
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.Ising.TIChoquetClose
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


theorem IsTailEvent.measurableSet {s : Set (ConfigSpace (Site d))} (hs : IsTailEvent s) :
    MeasurableSet s :=
  outsideSigma_le (box d 0) s (hs 0)


theorem IsTailEvent.compl {s : Set (ConfigSpace (Site d))} (hs : IsTailEvent s) :
    IsTailEvent sᶜ := fun n => (hs n).compl


theorem isTailEvent_univ : IsTailEvent (d := d) (Set.univ) :=
  fun n => @MeasurableSet.univ _ (outsideSigma (box d n))


theorem isTailEvent_empty : IsTailEvent (d := d) (∅ : Set (ConfigSpace (Site d))) :=
  fun n => @MeasurableSet.empty _ (outsideSigma (box d n))


theorem tic_restrict_compProd_trim_eq (β h : ℝ)
    (μ : Measure (ConfigSpace (Site d))) [IsFiniteMeasure μ]
    (hμ : IsDLRState d β h μ) {s : Set (ConfigSpace (Site d))} (hs : IsTailEvent s) (n : ℕ) :
    (((μ.restrict s).trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h))
      = @Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _
          ((outsideSigma (box d n)).prod inferInstance) (fun ω ↦ (id ω, id ω)) (μ.restrict s) := by
  set hm := outsideSigma_le (box d n) with hmdef
  set K := isingSpec n (bondFinsetTouch d n) β h with hKdef
  have hsn : @MeasurableSet _ (outsideSigma (box d n)) s := hs n
  have hf : @Measurable (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d))
      _ ((outsideSigma (box d n)).prod inferInstance) (fun ω => (id ω, id ω)) :=
    (measurable_id'' hm).prodMk measurable_id
  rw [tic_trim_restrict_comm μ hm s hsn, tic_compProd_restrict_left _ K s hsn,
    dlr_compProd_trim_eq β h μ hμ n]
  exact tic_map_diag_restrict μ s hsn hf


theorem tic_smul_compProd_trim_eq (β h : ℝ) (c : ENNReal) (hc : c ≠ ⊤)
    (μ : Measure (ConfigSpace (Site d))) [IsFiniteMeasure μ]
    (hμ : ∀ n, (μ.trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h)
      = @Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _
          ((outsideSigma (box d n)).prod inferInstance) (fun ω ↦ (id ω, id ω)) μ) (n : ℕ) :
    haveI : IsFiniteMeasure (c • μ) := μ.smul_finite hc
    ((c • μ).trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h)
      = @Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _
          ((outsideSigma (box d n)).prod inferInstance) (fun ω ↦ (id ω, id ω)) (c • μ) := by
  set hm := outsideSigma_le (box d n) with hmdef
  set K := isingSpec n (bondFinsetTouch d n) β h with hKdef
  set f : ConfigSpace (Site d) → ConfigSpace (Site d) × ConfigSpace (Site d) :=
    fun ω => (id ω, id ω) with hfdef
  have hf : @Measurable (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d))
      _ ((outsideSigma (box d n)).prod inferInstance) f :=
    (measurable_id'' hm).prodMk measurable_id
  rw [trim_smul μ hm c, Measure.compProd_smul_left, hμ n, Measure.map_smul]


theorem tic_isDLRState_cond_of_tail (β h : ℝ)
    (μ : Measure (ConfigSpace (Site d))) [IsFiniteMeasure μ]
    (hμ : IsDLRState d β h μ) {s : Set (ConfigSpace (Site d))} (hs : IsTailEvent s)
    (hs0 : μ s ≠ 0) :
    haveI : IsFiniteMeasure (μ[|s]) := inferInstance
    IsDLRState d β h (μ[|s]) := by
  
  haveI : IsFiniteMeasure (μ.restrict s) := inferInstance
  have hcne : (μ s)⁻¹ ≠ ⊤ := by
    simp only [ne_eq, ENNReal.inv_eq_top]; exact hs0
  haveI : IsFiniteMeasure ((μ s)⁻¹ • μ.restrict s) := (μ.restrict s).smul_finite hcne
  
  have hrestr := tic_restrict_compProd_trim_eq β h μ hμ hs
  
  have hscaled := tic_smul_compProd_trim_eq β h (μ s)⁻¹ hcne (μ.restrict s) hrestr
  have key : IsDLRState d β h ((μ s)⁻¹ • μ.restrict s) :=
    isDLRState_of_compProd_trim β h ((μ s)⁻¹ • μ.restrict s) hscaled
  
  
  exact key


theorem tic_cond_congr {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {s s' : Set Ω} (h : s =ᵐ[μ] s') : (μ[|s]) = (μ[|s']) := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, measure_congr h,
    Measure.restrict_congr_set h]


theorem tic_isDLRState_cond_of_aeTail (β h : ℝ)
    (μ : Measure (ConfigSpace (Site d))) [IsFiniteMeasure μ]
    (hμ : IsDLRState d β h μ) {s s' : Set (ConfigSpace (Site d))}
    (hs' : IsTailEvent s') (hae : s =ᵐ[μ] s') (hs0 : μ s ≠ 0) :
    haveI : IsFiniteMeasure (μ[|s]) := inferInstance
    IsDLRState d β h (μ[|s]) := by
  have hμeq : μ s' = μ s := (measure_congr hae).symm
  have hs0' : μ s' ≠ 0 := by rw [hμeq]; exact hs0
  have hcond : (μ[|s]) = (μ[|s']) := tic_cond_congr μ hae
  
  
  
  have key : IsDLRState d β h (μ[|s']) := tic_isDLRState_cond_of_tail β h μ hμ hs' hs0'
  simp only [hcond]
  exact key


open StatMech.ConfigSpace


theorem tic_plusState_closure_of_aeTail (β h : ℝ)
    (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))))
    {s s₁ s₂ : Set (ConfigSpace (Site d))} (hs1 : IsTailEvent s₁) (hs2 : IsTailEvent s₂)
    (haes : s =ᵐ[(plusState d β h : Measure (ConfigSpace (Site d)))] s₁)
    (haesc : sᶜ =ᵐ[(plusState d β h : Measure (ConfigSpace (Site d)))] s₂)
    (hs0 : (plusState d β h : Measure (ConfigSpace (Site d))) s ≠ 0)
    (hsc0 : (plusState d β h : Measure (ConfigSpace (Site d))) sᶜ ≠ 0) :
    IsDLRState d β h ((plusState d β h : Measure (ConfigSpace (Site d)))[|s])
      ∧ IsDLRState d β h ((plusState d β h : Measure (ConfigSpace (Site d)))[|sᶜ]) :=
  ⟨tic_isDLRState_cond_of_aeTail β h _ hdlr hs1 haes hs0,
   tic_isDLRState_cond_of_aeTail β h _ hdlr hs2 haesc hsc0⟩


theorem tic_minusState_closure_of_aeTail (β h : ℝ)
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
    {s s₁ s₂ : Set (ConfigSpace (Site d))} (hs1 : IsTailEvent s₁) (hs2 : IsTailEvent s₂)
    (haes : s =ᵐ[(minusState d β h : Measure (ConfigSpace (Site d)))] s₁)
    (haesc : sᶜ =ᵐ[(minusState d β h : Measure (ConfigSpace (Site d)))] s₂)
    (hs0 : (minusState d β h : Measure (ConfigSpace (Site d))) s ≠ 0)
    (hsc0 : (minusState d β h : Measure (ConfigSpace (Site d))) sᶜ ≠ 0) :
    IsDLRState d β h ((minusState d β h : Measure (ConfigSpace (Site d)))[|s])
      ∧ IsDLRState d β h ((minusState d β h : Measure (ConfigSpace (Site d)))[|sᶜ]) :=
  ⟨tic_isDLRState_cond_of_aeTail β h _ hdlr hs1 haes hs0,
   tic_isDLRState_cond_of_aeTail β h _ hdlr hs2 haesc hsc0⟩


theorem tic_plusState_isErgodic_of_aeTailInvariant (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))))
    (haeTail : ∀ s : Set (ConfigSpace (Site d)), MeasurableSet s →
      (∀ g : Multiplicative (Site d),
        (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) →
        ∃ s' : Set (ConfigSpace (Site d)), IsTailEvent (d := d) s'
          ∧ s =ᵐ[(plusState d β h : Measure (ConfigSpace (Site d)))] s') :
    IsErgodic (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) := by
  refine gec_plusState_isErgodic_of_closure β h hβ hh hti ?_
  intro s hs hinv hs0 hsc0
  have hinvc : ∀ g : Multiplicative (Site d),
      (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' sᶜ = sᶜ := fun g => by
    rw [Set.preimage_compl, hinv g]
  obtain ⟨s₁, hs1, haes⟩ := haeTail s hs hinv
  obtain ⟨s₂, hs2, haesc⟩ := haeTail sᶜ hs.compl hinvc
  exact tic_plusState_closure_of_aeTail β h hdlr hs1 hs2 haes haesc hs0 hsc0


theorem tic_minusState_isErgodic_of_aeTailInvariant (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
    (haeTail : ∀ s : Set (ConfigSpace (Site d)), MeasurableSet s →
      (∀ g : Multiplicative (Site d),
        (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) →
        ∃ s' : Set (ConfigSpace (Site d)), IsTailEvent (d := d) s'
          ∧ s =ᵐ[(minusState d β h : Measure (ConfigSpace (Site d)))] s') :
    IsErgodic (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))) := by
  refine gec_minusState_isErgodic_of_closure β h hβ hh hti ?_
  intro s hs hinv hs0 hsc0
  have hinvc : ∀ g : Multiplicative (Site d),
      (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' sᶜ = sᶜ := fun g => by
    rw [Set.preimage_compl, hinv g]
  obtain ⟨s₁, hs1, haes⟩ := haeTail s hs hinv
  obtain ⟨s₂, hs2, haesc⟩ := haeTail sᶜ hs.compl hinvc
  exact tic_minusState_closure_of_aeTail β h hdlr hs1 hs2 haes haesc hs0 hsc0

end Ising
end StatMech
