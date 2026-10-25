/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Def.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part9
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

open StatMech.Percolation

variable {d : ℕ}


theorem gvSwapPair_involutive {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout) :
    Function.Involutive (gvSwapPair (d := d) hsub) := by
  rintro ⟨σ, τ⟩
  simp only [gvSwapPair]
  rw [gvOvr_gvOvr_gvRes hsub σ τ, gvRes_gvOvr hsub σ τ]

theorem gvSwapPair_bijective {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout) :
    Function.Bijective (gvSwapPair (d := d) hsub) := (gvSwapPair_involutive hsub).bijective


theorem gv_consistency_double_sum {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (β h : ℝ) (g : ConfigSpace (Site d) → ℝ) :
    (∑ σ : {x // x ∈ Sout} → Bool, gvProb η Sout β h σ
        * ∑ τ : {x // x ∈ Sin} → Bool,
            gvProb (gvGlue η Sout σ) Sin β h τ * g (gvGlue (gvGlue η Sout σ) Sin τ))
      = ∑ σ : {x // x ∈ Sout} → Bool, gvProb η Sout β h σ * g (gvGlue η Sout σ) := by
  set F : (({x // x ∈ Sout} → Bool) × ({x // x ∈ Sin} → Bool)) → ℝ :=
    fun p => gvProb η Sout β h p.1
        * (gvProb (gvGlue η Sout p.1) Sin β h p.2 * g (gvGlue (gvGlue η Sout p.1) Sin p.2))
    with hF
  have hLHS : (∑ σ : {x // x ∈ Sout} → Bool, gvProb η Sout β h σ
        * ∑ τ : {x // x ∈ Sin} → Bool,
            gvProb (gvGlue η Sout σ) Sin β h τ * g (gvGlue (gvGlue η Sout σ) Sin τ))
      = ∑ p, F p := by
    rw [Fintype.sum_prod_type (f := F)]
    refine Finset.sum_congr rfl (fun σ _ => ?_); rw [Finset.mul_sum]
  rw [hLHS, ← Function.Bijective.sum_comp (gvSwapPair_bijective hsub) F]
  have hpoint : ∀ p : (({x // x ∈ Sout} → Bool) × ({x // x ∈ Sin} → Bool)),
      F (gvSwapPair hsub p)
        = gvProb η Sout β h p.1
            * (gvProb (gvGlue η Sout p.1) Sin β h p.2 * g (gvGlue η Sout p.1)) := by
    rintro ⟨σ, τ⟩
    simp only [hF, gvSwapPair]
    have harg : gvGlue (gvGlue η Sout (gvOvr hsub σ τ)) Sin (gvRes hsub σ) = gvGlue η Sout σ := by
      rw [gvGlue_gvGlue_eq_gvGlue_ovr hsub η (gvOvr hsub σ τ) (gvRes hsub σ),
        gvOvr_gvOvr_gvRes hsub σ τ]
    rw [harg]
    have hprob : gvProb η Sout β h (gvOvr hsub σ τ)
          * gvProb (gvGlue η Sout (gvOvr hsub σ τ)) Sin β h (gvRes hsub σ)
        = gvProb η Sout β h σ * gvProb (gvGlue η Sout σ) Sin β h τ := by
      unfold gvProb
      have hagree : ∀ x ∉ Sin, gvGlue η Sout (gvOvr hsub σ τ) x = gvGlue η Sout σ x :=
        fun x hx => gvGlue_ovr_eq_off hsub η σ τ hx
      rw [gv_fvZ_eq_of_agree_off β h hagree]
      have hw := gv_weight_spec_symm hsub η β h σ τ
      rw [div_mul_div_comm, div_mul_div_comm, hw]
    calc gvProb η Sout β h (gvOvr hsub σ τ)
            * (gvProb (gvGlue η Sout (gvOvr hsub σ τ)) Sin β h (gvRes hsub σ) * g (gvGlue η Sout σ))
        = (gvProb η Sout β h (gvOvr hsub σ τ)
              * gvProb (gvGlue η Sout (gvOvr hsub σ τ)) Sin β h (gvRes hsub σ))
            * g (gvGlue η Sout σ) := by ring
      _ = (gvProb η Sout β h σ * gvProb (gvGlue η Sout σ) Sin β h τ) * g (gvGlue η Sout σ) := by
            rw [hprob]
      _ = gvProb η Sout β h σ * (gvProb (gvGlue η Sout σ) Sin β h τ * g (gvGlue η Sout σ)) := by ring
  rw [Finset.sum_congr rfl (fun p _ => hpoint p), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  have hcollapse : (∑ τ : {x // x ∈ Sin} → Bool,
        gvProb η Sout β h σ * (gvProb (gvGlue η Sout σ) Sin β h τ * g (gvGlue η Sout σ)))
      = gvProb η Sout β h σ * g (gvGlue η Sout σ)
          * (∑ τ : {x // x ∈ Sin} → Bool, gvProb (gvGlue η Sout σ) Sin β h τ) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun τ _ => ?_); ring
  rw [hcollapse, gvProb_sum_eq_one (gvGlue η Sout σ) Sin β h, mul_one]


theorem iptp_gv_crossbox_dom {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    {A : Set (ConfigSpace (Site d))} (hAmeas : MeasurableSet A) (hAinc : IsIncreasing A) :
    (gvPlusMeasure Sout β h).real A ≤ (gvPlusMeasure Sin β h).real A := by
  set g0 : ConfigSpace (Site d) → ℝ := A.indicator (fun _ => (1:ℝ)) with hg0
  have hcds := gv_consistency_double_sum hsub (plusField d) β h g0
  have hpm : (gvPlusMeasure Sout β h).real A
      = ∑ σ : {x // x ∈ Sout} → Bool, gvProb (plusField d) Sout β h σ * g0 (gvGlue (plusField d) Sout σ) := by
    rw [gvPlusMeasure, gvMeasure_real_eq (plusField d) Sout β h hAmeas]
  rw [hpm, ← hcds]
  have hterm : ∀ σ : {x // x ∈ Sout} → Bool,
      gvProb (plusField d) Sout β h σ
        * ∑ τ : {x // x ∈ Sin} → Bool,
            gvProb (gvGlue (plusField d) Sout σ) Sin β h τ
              * g0 (gvGlue (gvGlue (plusField d) Sout σ) Sin τ)
      ≤ gvProb (plusField d) Sout β h σ * (gvPlusMeasure Sin β h).real A := by
    intro σ
    apply mul_le_mul_of_nonneg_left _ (gvProb_nonneg _ _ _ _ _)
    have hinner : (∑ τ : {x // x ∈ Sin} → Bool,
            gvProb (gvGlue (plusField d) Sout σ) Sin β h τ
              * g0 (gvGlue (gvGlue (plusField d) Sout σ) Sin τ))
        = (gvMeasure (gvGlue (plusField d) Sout σ) Sin β h).real A :=
      (gvMeasure_real_eq (gvGlue (plusField d) Sout σ) Sin β h hAmeas).symm
    rw [hinner]
    exact gvMeasure_le_plusField Sin hβ hh (gvGlue (plusField d) Sout σ) hAmeas hAinc
  calc ∑ σ : {x // x ∈ Sout} → Bool,
          gvProb (plusField d) Sout β h σ
            * ∑ τ : {x // x ∈ Sin} → Bool,
                gvProb (gvGlue (plusField d) Sout σ) Sin β h τ
                  * g0 (gvGlue (gvGlue (plusField d) Sout σ) Sin τ)
      ≤ ∑ σ : {x // x ∈ Sout} → Bool,
          gvProb (plusField d) Sout β h σ * (gvPlusMeasure Sin β h).real A :=
        Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (gvPlusMeasure Sin β h).real A := by
        rw [← Finset.sum_mul, gvProb_sum_eq_one (plusField d) Sout β h, one_mul]


end Ising
end StatMech
