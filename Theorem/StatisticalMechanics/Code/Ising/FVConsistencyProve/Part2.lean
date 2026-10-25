/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FVConsistencyProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PlusStateDLR.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Def.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


theorem swapPair_involutive {n m : ℕ} (hnm : n ≤ m) :
    Function.Involutive (swapPair (d := d) hnm) := by
  rintro ⟨σ, τ⟩
  simp only [swapPair]
  rw [ovrBox_ovrBox_resBox hnm σ τ, resBox_ovrBox hnm σ τ]

theorem swapPair_bijective {n m : ℕ} (hnm : n ≤ m) :
    Function.Bijective (swapPair (d := d) hnm) :=
  (swapPair_involutive hnm).bijective


theorem consistency_double_sum {n m : ℕ} (hnm : n ≤ m) (η : ConfigSpace (Site d)) (β h : ℝ)
    (g : ConfigSpace (Site d) → ℝ) :
    (∑ σ : {x // x ∈ box d m} → Bool,
        fvProb η m (bondFinsetTouch d m) β h σ
          * ∑ τ : {x // x ∈ box d n} → Bool,
              fvProb (glue η σ) n (bondFinsetTouch d n) β h τ * g (glue (glue η σ) τ))
      = ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb η m (bondFinsetTouch d m) β h σ * g (glue η σ) := by
  
  set F : (({x // x ∈ box d m} → Bool) × ({x // x ∈ box d n} → Bool)) → ℝ :=
    fun p => fvProb η m (bondFinsetTouch d m) β h p.1
        * (fvProb (glue η p.1) n (bondFinsetTouch d n) β h p.2 * g (glue (glue η p.1) p.2))
    with hF
  
  have hLHS : (∑ σ : {x // x ∈ box d m} → Bool,
        fvProb η m (bondFinsetTouch d m) β h σ
          * ∑ τ : {x // x ∈ box d n} → Bool,
              fvProb (glue η σ) n (bondFinsetTouch d n) β h τ * g (glue (glue η σ) τ))
      = ∑ p, F p := by
    rw [Fintype.sum_prod_type (f := F)]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.mul_sum]
  rw [hLHS]
  
  rw [← Function.Bijective.sum_comp (swapPair_bijective hnm) F]
  
  have hpoint : ∀ p : (({x // x ∈ box d m} → Bool) × ({x // x ∈ box d n} → Bool)),
      F (swapPair hnm p)
        = fvProb η m (bondFinsetTouch d m) β h p.1
            * (fvProb (glue η p.1) n (bondFinsetTouch d n) β h p.2 * g (glue η p.1)) := by
    rintro ⟨σ, τ⟩
    simp only [hF, swapPair]
    
    have harg : glue (glue η (ovrBox hnm σ τ)) (resBox hnm σ) = glue η σ := by
      rw [glue_glue_eq_glue_ovrBox hnm η (ovrBox hnm σ τ) (resBox hnm σ),
        ovrBox_ovrBox_resBox hnm σ τ]
    rw [harg]
    
    have hprob : fvProb η m (bondFinsetTouch d m) β h (ovrBox hnm σ τ)
          * fvProb (glue η (ovrBox hnm σ τ)) n (bondFinsetTouch d n) β h (resBox hnm σ)
        = fvProb η m (bondFinsetTouch d m) β h σ
          * fvProb (glue η σ) n (bondFinsetTouch d n) β h τ := by
      unfold fvProb
      
      have hagree : ∀ x ∉ box d n, glue η (ovrBox hnm σ τ) x = glue η σ x :=
        fun x hx => glue_ovrBox_eq_off_box hnm η σ τ hx
      rw [fvZ_eq_of_agree_off_box (bondFinsetTouch d n) β h hagree]
      have hw := fvWeight_spec_symm hnm η β h σ τ
      
      rw [div_mul_div_comm, div_mul_div_comm, hw]
    
    calc fvProb η m (bondFinsetTouch d m) β h (ovrBox hnm σ τ)
            * (fvProb (glue η (ovrBox hnm σ τ)) n (bondFinsetTouch d n) β h (resBox hnm σ)
                * g (glue η σ))
        = (fvProb η m (bondFinsetTouch d m) β h (ovrBox hnm σ τ)
              * fvProb (glue η (ovrBox hnm σ τ)) n (bondFinsetTouch d n) β h (resBox hnm σ))
            * g (glue η σ) := by ring
      _ = (fvProb η m (bondFinsetTouch d m) β h σ
              * fvProb (glue η σ) n (bondFinsetTouch d n) β h τ) * g (glue η σ) := by rw [hprob]
      _ = fvProb η m (bondFinsetTouch d m) β h σ
            * (fvProb (glue η σ) n (bondFinsetTouch d n) β h τ * g (glue η σ)) := by ring
  rw [Finset.sum_congr rfl (fun p _ => hpoint p)]
  
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  have hcollapse : (∑ τ : {x // x ∈ box d n} → Bool,
        fvProb η m (bondFinsetTouch d m) β h σ
          * (fvProb (glue η σ) n (bondFinsetTouch d n) β h τ * g (glue η σ)))
      = fvProb η m (bondFinsetTouch d m) β h σ * g (glue η σ)
          * (∑ τ : {x // x ∈ box d n} → Bool, fvProb (glue η σ) n (bondFinsetTouch d n) β h τ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    ring
  rw [hcollapse, fvProb_sum_eq_one (glue η σ) n (bondFinsetTouch d n) β h, mul_one]


theorem fvConsistency_plus (β h : ℝ) : FVConsistency d β h := by
  intro n m hnm f
  
  rw [plusMeasure_coe,
    integral_fvMeasure_eq_sum (plusField d) m (bondFinsetTouch d m) β h
      (specApply n (bondFinsetTouch d n) β h (f : ConfigSpace (Site d) → ℝ)),
    integral_fvMeasure_eq_sum (plusField d) m (bondFinsetTouch d m) β h
      (f : ConfigSpace (Site d) → ℝ)]
  
  simp only [specApply_eq_sum]
  
  exact consistency_double_sum hnm (plusField d) β h (f : ConfigSpace (Site d) → ℝ)


theorem psdlr_plusState_isDLR_uncond (β h : ℝ) :
    IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))) :=
  psdlr_plusState_isDLR β h (fvConsistency_plus β h)

end Ising
end StatMech
