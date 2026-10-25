/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Away.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology


namespace SheafCohomology

section SheafCondition

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- `f` becomes a unit in `A[(fg)⁻¹]`. -/
lemma isUnit_algebraMap_of_away_mul_left :
    IsUnit (algebraMap A (Localization.Away (f * g)) f) := by
  have hu := IsLocalization.map_units (Localization.Away (f * g))
    (⟨f * g, 1, pow_one _⟩ : Submonoid.powers (f * g))
  simp at hu; exact hu.1

/-- `g` becomes a unit in `A[(fg)⁻¹]`. -/
lemma isUnit_algebraMap_of_away_mul_right :
    IsUnit (algebraMap A (Localization.Away (f * g)) g) := by
  have hu := IsLocalization.map_units (Localization.Away (f * g))
    (⟨f * g, 1, pow_one _⟩ : Submonoid.powers (f * g))
  simp at hu; exact hu.2

end SheafCondition
end SheafCohomology
