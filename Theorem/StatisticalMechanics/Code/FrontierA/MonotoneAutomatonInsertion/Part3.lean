/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part3
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInsertion.Part3
open MeasureTheory
open scoped ENNReal NNReal


namespace StatMech.FrontierA

open StatMech.Lattice

variable {d : ℕ}


@[simp] theorem forceSitesOccupied_apply (S : Finset (Site d))
    (eta : ConfigSpace (Site d)) (y : Site d) :
    forceSitesOccupied S eta y = if y ∈ S then true else eta y :=
  rfl

@[simp] theorem forceSitesOccupied_empty (eta : ConfigSpace (Site d)) :
    forceSitesOccupied (∅ : Finset (Site d)) eta = eta := by
  funext y
  simp [forceSitesOccupied]

theorem forceSitesOccupied_insert (x : Site d) (S : Finset (Site d)) :
    (forceSitesOccupied (insert x S) :
      ConfigSpace (Site d) → ConfigSpace (Site d)) =
      forceSiteOccupied x ∘ forceSitesOccupied S := by
  funext eta y
  by_cases hyx : y = x
  · subst y
    simp [forceSitesOccupied, forceSiteOccupied]
  · simp [forceSitesOccupied, forceSiteOccupied, hyx]

theorem measurable_forceSitesOccupied (S : Finset (Site d)) :
    Measurable (forceSitesOccupied S :
      ConfigSpace (Site d) → ConfigSpace (Site d)) := by
  rw [measurable_pi_iff]
  intro y
  by_cases h : y ∈ S
  · simp [forceSitesOccupied, h]
  · simpa [forceSitesOccupied, h] using (measurable_pi_apply y)


theorem forceSitesOccupied_map_absolutelyContinuous
    (nu : Measure (ConfigSpace (Site d))) (epsilon : ℝ≥0∞)
    (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon) (S : Finset (Site d)) :
    nu.map (forceSitesOccupied S) ≪ nu := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [show (forceSitesOccupied (∅ : Finset (Site d)) :
        ConfigSpace (Site d) → ConfigSpace (Site d)) = id by
          funext eta
          exact forceSitesOccupied_empty eta]
      simpa using Measure.absolutelyContinuous_refl nu
  | @insert x S hx ih =>
      rw [forceSitesOccupied_insert,
        ← Measure.map_map (measurable_forceSiteOccupied x)
          (measurable_forceSitesOccupied S)]
      exact (ih.map (measurable_forceSiteOccupied x)).trans
        (forceSiteOccupied_map_absolutelyContinuous nu epsilon hepsilon hinsert x)


theorem positive_of_forceSitesOccupied_preimage
    (nu : Measure (ConfigSpace (Site d))) (epsilon : ℝ≥0∞)
    (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon)
    (S : Finset (Site d))
    {A B : Set (ConfigSpace (Site d))} (hBmeas : MeasurableSet B)
    (hsub : A ⊆ (forceSitesOccupied S) ⁻¹' B) (hApos : 0 < nu A) :
    0 < nu B := by
  by_contra hBpos
  rw [not_lt, nonpos_iff_eq_zero] at hBpos
  have hac := forceSitesOccupied_map_absolutelyContinuous
    nu epsilon hepsilon hinsert S
  have hmapZero : nu.map (forceSitesOccupied S) B = 0 := hac hBpos
  have hpreZero : nu ((forceSitesOccupied S) ⁻¹' B) = 0 := by
    rw [← Measure.map_apply (measurable_forceSitesOccupied S) hBmeas]
    exact hmapZero
  have hAle : nu A ≤ nu ((forceSitesOccupied S) ⁻¹' B) := measure_mono hsub
  rw [hpreZero] at hAle
  exact (not_lt_of_ge hAle) hApos

end StatMech.FrontierA
