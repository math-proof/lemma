/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.GrandCoupling.Part3
import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part6
import Def.StatisticalMechanics.Code.OSSS.GrandCouplingAssembly.Part4
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace GrandCouplingAssembly

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling StatMech.Probability

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma selMap_eq_Wt (n s : ℕ) (U V : Fin n → ℝ) : selMap n s (U, V) = Wt U V s := by
  funext i
  unfold selMap projInl Wt
  rw [MeasurableEquiv.coe_piCongrLeft]
  simp only [Equiv.piCongrLeft_apply, eq_rec_constant]
  rw [swEquiv_symm_apply, combine_apply]
  unfold sw
  by_cases h : (i:ℕ) < s <;> simp [h]


lemma selMap_measurePreserving (n s : ℕ) :
    MeasurePreserving (selMap n s) ((Vcube n).prod (Vcube n)) (Vcube n) := by
  show MeasurePreserving (selMap n s)
    ((Measure.pi (fun _ : Fin n => unitMeasure)).prod (Measure.pi (fun _ : Fin n => unitMeasure)))
    (Measure.pi (fun _ : Fin n => unitMeasure))
  have hcombine : MeasurePreserving (combine n)
      ((Measure.pi (fun _ : Fin n => unitMeasure)).prod (Measure.pi (fun _ : Fin n => unitMeasure)))
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure)) :=
    (measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin n => ℝ)
      (fun _ : Fin n ⊕ Fin n => unitMeasure)).symm _
  have hperm : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin n => ℝ) (swEquiv n s))
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure))
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure)) := by
    have h := measurePreserving_piCongrLeft (fun _ : Fin n ⊕ Fin n => unitMeasure) (swEquiv n s)
    convert h using 2
  have hproj : MeasurePreserving (projInl n)
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure))
      (Measure.pi (fun _ : Fin n => unitMeasure)) := by
    have hsum := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin n => ℝ)
      (fun _ : Fin n ⊕ Fin n => unitMeasure)
    have hfst : MeasurePreserving Prod.fst
        ((Measure.pi (fun _ : Fin n => unitMeasure)).prod (Measure.pi (fun _ : Fin n => unitMeasure)))
        (Measure.pi (fun _ : Fin n => unitMeasure)) := measurePreserving_fst
    have := hfst.comp hsum
    convert this using 1
  have := (hproj.comp hperm).comp hcombine
  convert this using 1


theorem integral_g_codeMap_Wt (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) (s : ℕ) :
    ∫ p, g (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s)) ∂((Vcube n).prod (Vcube n))
      = ∑ x, g x * μ x := by
  have hmp := selMap_measurePreserving n s
  have hae : AEStronglyMeasurable (fun w => g (codeMap μ (σ : Fin n → E) w)) (Vcube n) :=
    (measurable_g_codeMap μ σ g).aestronglyMeasurable
  have hcomp : ∫ p, (fun w => g (codeMap μ (σ : Fin n → E) w)) (selMap n s p)
        ∂((Vcube n).prod (Vcube n))
      = ∫ w, g (codeMap μ (σ : Fin n → E) w) ∂(Vcube n) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable, hmp.map_eq]
    rwa [hmp.map_eq]
  have hrw : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        (fun w => g (codeMap μ (σ : Fin n → E) w)) (selMap n s p))
      = (fun p => g (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s))) := by
    funext p; rw [show p = (p.1, p.2) from rfl, selMap_eq_Wt]
  rw [hrw] at hcomp
  rw [hcomp, integral_g_codeMap μ hpos hμ1 σ g]


lemma Wt_mono_prod {n : ℕ} (s : ℕ) :
    Monotone (fun p : (Fin n → ℝ) × (Fin n → ℝ) => Wt p.1 p.2 s) := by
  intro p p' hpp i
  unfold Wt
  rw [Prod.le_def] at hpp
  by_cases h : (i:ℕ) < s
  · simp only [h, if_true]; exact hpp.2 i
  · simp only [h, if_false]; exact hpp.1 i


lemma f_codeMap_Wt_mono_prod {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (s : ℕ) :
    Monotone (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (codeMap μ σ (Wt p.1 p.2 s))) :=
  fun _ _ hpp => hf ((codeMap_mono_u hpos hmono σ) ((Wt_mono_prod s) hpp))


lemma coord_codeMap_Wt_mono_prod {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E) (e : E) (s : ℕ) :
    Monotone (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Lindeberg.coord e (codeMap μ σ (Wt p.1 p.2 s))) :=
  fun _ _ hpp => Lindeberg.coord_mono e ((codeMap_mono_u hpos hmono σ) ((Wt_mono_prod s) hpp))


lemma measurable_g_codeMap_Wt_prod (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) (s : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        g (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s))) := by
  apply (measurable_g_codeMap μ σ g).comp
  apply measurable_pi_lambda
  intro i; unfold Wt
  by_cases h : (i:ℕ) < s
  · simp only [h, if_true]; exact (measurable_pi_apply i).comp measurable_snd
  · simp only [h, if_false]; exact (measurable_pi_apply i).comp measurable_fst


end GrandCouplingAssembly
end OSSS
end StatMech
