/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSiteBond.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw.Part4
open MeasureTheory
open scoped NNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


theorem automatonBondLaw_eq_map_siteToBond (T : MonotoneAutomaton d)
    (mu : Measure (NonnegativeField d)) :
    automatonBondLaw T mu = Measure.map siteToBond (automatonSiteLaw T mu) := by
  unfold automatonBondLaw automatonSiteLaw
  rw [Measure.map_map measurable_siteToBond T.measurable_toFun]


theorem automatonSiteLaw_isTranslationInvariant (T : MonotoneAutomaton d)
    (mu : Measure (NonnegativeField d))
    (hinv : IsFieldTranslationInvariant mu) :
    IsTranslationInvariant (G := Multiplicative (Site d))
      (automatonSiteLaw T mu) := by
  intro g
  refine ⟨measurable_shift g, ?_⟩
  unfold automatonSiteLaw
  rw [Measure.map_map (measurable_shift g) T.measurable_toFun]
  have hcomp :
      (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ∘ T =
        T ∘ (fieldShift g : NonnegativeField d → NonnegativeField d) := by
    funext xi
    exact (T.equivariant g xi).symm
  rw [hcomp, ← Measure.map_map T.measurable_toFun (measurable_fieldShift g),
    (hinv g).map_eq]


theorem automatonSiteLaw_isErgodic (T : MonotoneAutomaton d)
    (mu : Measure (NonnegativeField d)) (herg : IsFieldErgodic mu) :
    IsErgodic (G := Multiplicative (Site d)) (automatonSiteLaw T mu) := by
  refine ⟨automatonSiteLaw_isTranslationInvariant T mu herg.1, ?_⟩
  intro s hs hinv
  have hpreMeas : MeasurableSet (T ⁻¹' s) := T.measurable_toFun hs
  have hpreInv : ∀ g : Multiplicative (Site d),
      (fieldShift g : NonnegativeField d → NonnegativeField d) ⁻¹' (T ⁻¹' s) =
        T ⁻¹' s := by
    intro g
    ext xi
    simp only [Set.mem_preimage]
    rw [T.equivariant, ← Set.mem_preimage, hinv g]
  rcases herg.2 _ hpreMeas hpreInv with hzero | hfull
  · left
    rwa [automatonSiteLaw, Measure.map_apply T.measurable_toFun hs]
  · right
    rw [automatonSiteLaw, Measure.map_apply T.measurable_toFun hs, hfull,
      Measure.map_apply T.measurable_toFun MeasurableSet.univ]
    rfl


theorem automatonBondLaw_isTranslationInvariant (T : MonotoneAutomaton d)
    (mu : Measure (NonnegativeField d))
    (hinv : IsFieldTranslationInvariant mu) :
    IsTranslationInvariant (G := Multiplicative (Site d))
      (automatonBondLaw T mu) := by
  rw [automatonBondLaw_eq_map_siteToBond]
  exact siteToBond_isTranslationInvariant _
    (automatonSiteLaw_isTranslationInvariant T mu hinv)


theorem automatonBondLaw_isErgodic (T : MonotoneAutomaton d)
    (mu : Measure (NonnegativeField d)) (herg : IsFieldErgodic mu) :
    IsErgodic (G := Multiplicative (Site d)) (automatonBondLaw T mu) := by
  rw [automatonBondLaw_eq_map_siteToBond]
  exact siteToBond_isErgodic _ (automatonSiteLaw_isErgodic T mu herg)

end StatMech.FrontierA
