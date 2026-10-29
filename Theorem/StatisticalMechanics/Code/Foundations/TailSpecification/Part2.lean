/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.AeTailInvariant.Part4
import Def.StatisticalMechanics.Code.Foundations.TailSpecification
open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped ENNReal

set_option linter.unusedSectionVars false


namespace StatMech

open ConfigSpace

variable {E : Type*} [Countable E]


theorem ts_restrict_state
    {window : ℕ → Set E}
    {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E)
      (outsideSigma (window n)) inferInstance}
    [∀ n, IsSFiniteKernel (K n)]
    (mu : Measure (ConfigSpace E)) [IsFiniteMeasure mu]
    (hmu : IsTailSpecificationState window K mu)
    {s : Set (ConfigSpace E)} (hs : AtiTailEvent window s) (n : ℕ) :
    ((mu.restrict s).trim (outsideSigma_le (window n))) ⊗ₘ K n =
      @Measure.map (ConfigSpace E) (ConfigSpace E × ConfigSpace E) _
        ((outsideSigma (window n)).prod inferInstance)
        (fun omega => (id omega, id omega)) (mu.restrict s) := by
  set hm := outsideSigma_le (window n)
  have hsn : @MeasurableSet _ (outsideSigma (window n)) s := hs n
  have hf : @Measurable (ConfigSpace E) (ConfigSpace E × ConfigSpace E) _
      ((outsideSigma (window n)).prod inferInstance)
      (fun omega => (id omega, id omega)) :=
    (measurable_id'' hm).prodMk measurable_id
  rw [ts_trim_restrict_comm mu hm s hsn,
    ts_compProd_restrict_left _ (K n) s hsn, hmu n]
  exact ts_map_diag_restrict mu s hsn hf

theorem ts_smul_state
    {window : ℕ → Set E}
    {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E)
      (outsideSigma (window n)) inferInstance}
    [∀ n, IsSFiniteKernel (K n)]
    (c : ENNReal) (hc : c ≠ ⊤)
    (mu : Measure (ConfigSpace E)) [IsFiniteMeasure mu]
    (hmu : IsTailSpecificationState window K mu) :
    haveI : IsFiniteMeasure (c • mu) := mu.smul_finite hc
    IsTailSpecificationState window K (c • mu) := by
  intro n
  have hf : @Measurable (ConfigSpace E) (ConfigSpace E × ConfigSpace E) _
      ((outsideSigma (window n)).prod inferInstance)
      (fun omega => (id omega, id omega)) :=
    (measurable_id'' (outsideSigma_le (window n))).prodMk measurable_id
  rw [ts_trim_smul mu (outsideSigma_le (window n)) c,
    Measure.compProd_smul_left, hmu n, Measure.map_smul]


theorem ts_cond_state
    {window : ℕ → Set E}
    {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E)
      (outsideSigma (window n)) inferInstance}
    [∀ n, IsSFiniteKernel (K n)]
    (mu : Measure (ConfigSpace E)) [IsFiniteMeasure mu]
    (hmu : IsTailSpecificationState window K mu)
    {s : Set (ConfigSpace E)} (hs : AtiTailEvent window s)
    (hs0 : mu s ≠ 0) :
    IsTailSpecificationState window K (mu[|s]) := by
  haveI : IsFiniteMeasure (mu.restrict s) := inferInstance
  have hc : (mu s)⁻¹ ≠ ⊤ := by
    simp only [ne_eq, ENNReal.inv_eq_top]
    exact hs0
  have hrestrict : IsTailSpecificationState window K (mu.restrict s) := by
    intro n
    exact ts_restrict_state mu hmu hs n
  have hscaled := ts_smul_state (mu s)⁻¹ hc (mu.restrict s) hrestrict
  exact hscaled

theorem ts_cond_congr {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {s t : Set Omega} (h : s =ᵐ[mu] t) :
    (mu[|s]) = (mu[|t]) := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, measure_congr h,
    Measure.restrict_congr_set h]


theorem ts_cond_state_of_ae_tail
    {window : ℕ → Set E}
    {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E)
      (outsideSigma (window n)) inferInstance}
    [∀ n, IsSFiniteKernel (K n)]
    (mu : Measure (ConfigSpace E)) [IsFiniteMeasure mu]
    (hmu : IsTailSpecificationState window K mu)
    {s t : Set (ConfigSpace E)} (ht : AtiTailEvent window t)
    (hae : s =ᵐ[mu] t) (hs0 : mu s ≠ 0) :
    IsTailSpecificationState window K (mu[|s]) := by
  have hmass : mu t = mu s := (measure_congr hae).symm
  have ht0 : mu t ≠ 0 := by
    rw [hmass]
    exact hs0
  have hcond : (mu[|s]) = (mu[|t]) := ts_cond_congr mu hae
  have htail := ts_cond_state mu hmu ht ht0
  simpa only [hcond] using htail

end StatMech
