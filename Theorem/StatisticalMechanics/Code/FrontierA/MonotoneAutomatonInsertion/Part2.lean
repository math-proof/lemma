/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part3
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInsertion.Part2
open MeasureTheory
open scoped ENNReal NNReal


namespace StatMech.FrontierA

open StatMech.Lattice

variable {d : ℕ}


@[simp] theorem forceSiteOccupied_self (x : Site d)
    (eta : ConfigSpace (Site d)) : forceSiteOccupied x eta x = true := by
  simp [forceSiteOccupied]

@[simp] theorem forceSiteOccupied_apply_of_ne {x y : Site d} (h : y ≠ x)
    (eta : ConfigSpace (Site d)) : forceSiteOccupied x eta y = eta y := by
  simp [forceSiteOccupied, h]

theorem measurable_forceSiteOccupied (x : Site d) :
    Measurable (forceSiteOccupied x :
      ConfigSpace (Site d) → ConfigSpace (Site d)) := by
  rw [measurable_pi_iff]
  intro y
  by_cases h : y = x
  · subst y
    simp [forceSiteOccupied]
  · simpa [forceSiteOccupied, h] using (measurable_pi_apply y)


theorem forceSiteOccupied_eq_self_of_eq_true (x : Site d)
    (eta : ConfigSpace (Site d)) (h : eta x = true) :
    forceSiteOccupied x eta = eta := by
  funext y
  by_cases hy : y = x
  · subst y
    simp [h]
  · simp [forceSiteOccupied, hy]


theorem siteEventIgnores_forceSiteOccupied_preimage (x : Site d)
    (B : Set (ConfigSpace (Site d))) :
    SiteEventIgnores x ((forceSiteOccupied x) ⁻¹' B) := by
  intro eta eta' hagree
  have heq : forceSiteOccupied x eta = forceSiteOccupied x eta' := by
    funext y
    by_cases hy : y = x
    · subst y
      simp
    · simp [forceSiteOccupied, hy, hagree y hy]
  rw [Set.mem_preimage, Set.mem_preimage, heq]


theorem forceSiteOccupied_map_absolutelyContinuous
    (nu : Measure (ConfigSpace (Site d))) (epsilon : ENNReal)
    (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon) (x : Site d) :
    nu.map (forceSiteOccupied x) ≪ nu := by
  apply Measure.AbsolutelyContinuous.mk
  intro B hBmeas hBzero
  rw [Measure.map_apply (measurable_forceSiteOccupied x) hBmeas]
  let A : Set (ConfigSpace (Site d)) := (forceSiteOccupied x) ⁻¹' B
  have hAmeas : MeasurableSet A := measurable_forceSiteOccupied x hBmeas
  have hAoff : SiteEventIgnores x A :=
    siteEventIgnores_forceSiteOccupied_preimage x B
  have hle := hinsert x A hAmeas hAoff
  have hsub : A ∩ {eta : ConfigSpace (Site d) | eta x = true} ⊆ B := by
    rintro eta ⟨hetaB, hetaOpen⟩
    have hfix := forceSiteOccupied_eq_self_of_eq_true x eta hetaOpen
    simpa only [A, Set.mem_preimage, hfix] using hetaB
  have hinterZero : nu (A ∩ {eta : ConfigSpace (Site d) | eta x = true}) = 0 :=
    measure_mono_null hsub hBzero
  rw [hinterZero] at hle
  have hmul : epsilon * nu A = 0 := nonpos_iff_eq_zero.mp hle
  exact (mul_eq_zero.mp hmul).resolve_left hepsilon


end StatMech.FrontierA
