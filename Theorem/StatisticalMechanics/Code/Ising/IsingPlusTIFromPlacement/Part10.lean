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
import Def.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part10
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


theorem iptp_gvBondTouch_boxFinset (n : ℕ) :
    gvBondTouch (boxFinset d n) = bondFinsetTouch d n := by
  apply Finset.Subset.antisymm
  · intro e he
    rw [gvBondTouch, Finset.mem_image] at he
    obtain ⟨p, hp, rfl⟩ := he
    rw [Finset.mem_filter] at hp
    obtain ⟨_, hadj, htouch⟩ := hp
    refine StatMech.Lattice.mk_mem_bondFinsetTouch hadj ?_
    rcases htouch with h | h
    · exact Or.inl (mem_boxFinset.mp h)
    · exact Or.inr (mem_boxFinset.mp h)
  · intro e he
    rw [bondFinsetTouch, Finset.mem_image] at he
    obtain ⟨p, hp, rfl⟩ := he
    rw [bondPairsTouch, Finset.mem_filter] at hp
    obtain ⟨_, hadj, htouch⟩ := hp
    refine gv_mk_mem_bondTouch hadj ?_
    rcases htouch with h | h
    · exact Or.inl (mem_boxFinset.mpr h)
    · exact Or.inr (mem_boxFinset.mpr h)

theorem iptp_gvGlue_box (n : ℕ) (η : ConfigSpace (Site d)) (τ : {x // x ∈ box d n} → Bool) :
    gvGlue η (boxFinset d n) (fun y => τ ((iptp_boxEquiv d n).symm y)) = glue η τ := by
  funext x
  by_cases hx : x ∈ box d n
  · rw [gvGlue_mem _ _ _ (mem_boxFinset.mpr hx), glue_mem _ _ hx]; congr 1
  · rw [gvGlue_not_mem _ _ _ (fun h => hx (mem_boxFinset.mp h)), glue_not_mem _ _ hx]

theorem iptp_gvEnergy_box (n : ℕ) (η : ConfigSpace (Site d)) (h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    gvEnergy η (boxFinset d n) h (fun y => τ ((iptp_boxEquiv d n).symm y))
      = fvEnergy η n (bondFinsetTouch d n) h τ := by
  unfold gvEnergy fvEnergy
  rw [iptp_gvBondTouch_boxFinset, iptp_gvGlue_box]

theorem iptp_gvWeight_box (n : ℕ) (η : ConfigSpace (Site d)) (β h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    gvWeight η (boxFinset d n) β h (fun y => τ ((iptp_boxEquiv d n).symm y))
      = fvWeight η n (bondFinsetTouch d n) β h τ := by
  unfold gvWeight fvWeight; rw [iptp_gvEnergy_box]

theorem iptp_gvZ_box (n : ℕ) (η : ConfigSpace (Site d)) (β h : ℝ) :
    gvZ η (boxFinset d n) β h = fvZ η n (bondFinsetTouch d n) β h := by
  unfold gvZ fvZ
  rw [← Equiv.sum_comp (Equiv.arrowCongr (iptp_boxEquiv d n) (Equiv.refl Bool))
    (fun τ => gvWeight η (boxFinset d n) β h τ)]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [← iptp_gvWeight_box n η β h τ]; rfl

theorem iptp_gvProb_box (n : ℕ) (η : ConfigSpace (Site d)) (β h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    gvProb η (boxFinset d n) β h (fun y => τ ((iptp_boxEquiv d n).symm y))
      = fvProb η n (bondFinsetTouch d n) β h τ := by
  unfold gvProb fvProb; rw [iptp_gvWeight_box, iptp_gvZ_box]


theorem iptp_gvMeasure_eq_fvMeasure (n : ℕ) (η : ConfigSpace (Site d)) (β h : ℝ) :
    gvMeasure η (boxFinset d n) β h = fvMeasure η n (bondFinsetTouch d n) β h := by
  unfold gvMeasure fvMeasure
  rw [← Equiv.sum_comp (Equiv.arrowCongr (iptp_boxEquiv d n) (Equiv.refl Bool))
    (fun τ => ENNReal.ofReal (gvProb η (boxFinset d n) β h τ)
      • Measure.dirac (gvGlue η (boxFinset d n) τ))]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [show gvProb η (boxFinset d n) β h ((Equiv.arrowCongr (iptp_boxEquiv d n) (Equiv.refl Bool)) τ)
        = fvProb η n (bondFinsetTouch d n) β h τ from iptp_gvProb_box n η β h τ,
    show gvGlue η (boxFinset d n) ((Equiv.arrowCongr (iptp_boxEquiv d n) (Equiv.refl Bool)) τ)
        = glue η τ from iptp_gvGlue_box n η τ]


theorem iptp_gvPlusMeasure_eq_plusMeasure (n : ℕ) (β h : ℝ) :
    gvPlusMeasure (boxFinset d n) β h = (plusMeasure d n β h : Measure (ConfigSpace (Site d))) := by
  rw [gvPlusMeasure, iptp_gvMeasure_eq_fvMeasure, plusMeasure_coe]


end Ising
end StatMech
