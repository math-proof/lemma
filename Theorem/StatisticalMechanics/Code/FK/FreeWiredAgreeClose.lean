/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWiredAgreeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FreeIVErgodicClose.Part2
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Theorem.StatisticalMechanics.Code.FK.FKTwoBoxDecoupling.Part2
import Theorem.StatisticalMechanics.Code.FK.CrossBoxGeneralKeystone.Part3
import Theorem.StatisticalMechanics.Code.FK.FKLimitsErgodicUncond
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}


theorem fwa_freeIV_congr (d : ℕ) {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp1₁ : p₁ < 1)
    (hp₂ : 0 < p₂) (hp1₂ : p₂ < 1) (heq : p₁ = p₂) :
    (freeInfiniteVolume d hp₁ hp1₁ (by norm_num : (0:ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d))))
    = (freeInfiniteVolume d hp₂ hp1₂ (by norm_num : (0:ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d)))) := by subst heq; rfl


theorem fwa_wiredIV_congr (d : ℕ) {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp1₁ : p₁ < 1)
    (hp₂ : 0 < p₂) (hp1₂ : p₂ < 1) (heq : p₁ = p₂) :
    (wiredInfiniteVolume d hp₁ hp1₁ (by norm_num : (0:ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d))))
    = (wiredInfiniteVolume d hp₂ hp1₂ (by norm_num : (0:ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d)))) := by subst heq; rfl


theorem fwa_eventMassProb_free_at_p (d N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    eventMassProb (fuc_freeMass d N (fsc_logit p)) A
      = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
  rw [fuc_eventMassProb_free,
    fwa_freeIV_congr d (fsc_logistic_pos _) (fsc_logistic_lt_one _) hp hp1
      (fsc_logistic_logit hp hp1)]


theorem fwa_eventMassProb_wired_at_p (d N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    eventMassProb (fuc_wiredMass d N (fsc_logit p)) A
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
  rw [fuc_eventMassProb_wired,
    fwa_wiredIV_congr d (fsc_logistic_pos _) (fsc_logistic_lt_one _) hp hp1
      (fsc_logistic_logit hp hp1)]


theorem fwa_edgeIncl_boxVertInclLE {N m : ℕ} (h : N ≤ m) (e : Sym2 (boxVerts d N)) :
    edgeIncl d m (Sym2.map (boxVertInclLE d h) e) = edgeIncl d N e := by
  unfold edgeIncl
  rw [Sym2.map_map]
  congr 1


theorem fwa_rerealise {N m : ℕ} (h : N ≤ m) (t₀ : Finset (Sym2 (boxVerts d N))) :
    t₀.image (edgeIncl d N) = (t₀.image (Sym2.map (boxVertInclLE d h))).image (edgeIncl d m) := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro e _
  simp only [Function.comp_apply]
  exact (fwa_edgeIncl_boxVertInclLE h e).symm


end FK
end StatMech
