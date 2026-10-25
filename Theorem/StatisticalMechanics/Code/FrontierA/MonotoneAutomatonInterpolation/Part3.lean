/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw.Part4
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part3
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


theorem interpolatedBondLaw_eq_map_siteToBond (T : MonotoneAutomaton d)
    (mu : Measure (FieldTriple d)) :
    interpolatedBondLaw T mu =
      Measure.map siteToBond (interpolatedSiteLaw T mu) := by
  unfold interpolatedBondLaw interpolatedSiteLaw
  rw [Measure.map_map measurable_siteToBond (measurable_interpolatedSite T)]


theorem interpolatedSiteLaw_isTranslationInvariant (T : MonotoneAutomaton d)
    (mu : Measure (FieldTriple d))
    (hinv : IsTripleFieldTranslationInvariant mu) :
    IsTranslationInvariant (G := Multiplicative (Site d))
      (interpolatedSiteLaw T mu) := by
  intro g
  refine ⟨measurable_shift g, ?_⟩
  unfold interpolatedSiteLaw
  rw [Measure.map_map (measurable_shift g) (measurable_interpolatedSite T)]
  have hcomp :
      (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ∘ interpolatedSite T =
        interpolatedSite T ∘ (tripleFieldShift g : FieldTriple d → FieldTriple d) := by
    funext q
    exact (interpolatedSite_shift T g q).symm
  rw [hcomp,
    ← Measure.map_map (measurable_interpolatedSite T) (measurable_tripleFieldShift g),
    (hinv g).map_eq]


theorem interpolatedSiteLaw_isErgodic (T : MonotoneAutomaton d)
    (mu : Measure (FieldTriple d)) (herg : IsTripleFieldErgodic mu) :
    IsErgodic (G := Multiplicative (Site d)) (interpolatedSiteLaw T mu) := by
  refine ⟨interpolatedSiteLaw_isTranslationInvariant T mu herg.1, ?_⟩
  intro s hs hinv
  have hpreMeas : MeasurableSet ((interpolatedSite T) ⁻¹' s) :=
    measurable_interpolatedSite T hs
  have hpreInv : ∀ g : Multiplicative (Site d),
      (tripleFieldShift g : FieldTriple d → FieldTriple d) ⁻¹'
          ((interpolatedSite T) ⁻¹' s) = (interpolatedSite T) ⁻¹' s := by
    intro g
    ext q
    simp only [Set.mem_preimage]
    rw [interpolatedSite_shift, ← Set.mem_preimage, hinv g]
  rcases herg.2 _ hpreMeas hpreInv with hzero | hfull
  · left
    rwa [interpolatedSiteLaw,
      Measure.map_apply (measurable_interpolatedSite T) hs]
  · right
    rw [interpolatedSiteLaw,
      Measure.map_apply (measurable_interpolatedSite T) hs, hfull,
      Measure.map_apply (measurable_interpolatedSite T) MeasurableSet.univ]
    rfl


theorem interpolatedBondLaw_isErgodic (T : MonotoneAutomaton d)
    (mu : Measure (FieldTriple d)) (herg : IsTripleFieldErgodic mu) :
    IsErgodic (G := Multiplicative (Site d)) (interpolatedBondLaw T mu) := by
  rw [interpolatedBondLaw_eq_map_siteToBond]
  exact siteToBond_isErgodic _ (interpolatedSiteLaw_isErgodic T mu herg)

end StatMech.FrontierA
