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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology


namespace SheafCohomology

section SheafCondition

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- The restriction `A[f⁻¹] → A[(fg)⁻¹]` induced by the universal property
of localization. This is one of the two Čech restriction maps for `{D(f), D(g)}`. -/
noncomputable def cechMapFromF :
    Localization.Away f →+* Localization.Away (f * g) :=
  Localization.awayLift (algebraMap A (Localization.Away (f * g))) f
    (isUnit_algebraMap_of_away_mul_left A f g)

/-- The restriction `A[g⁻¹] → A[(fg)⁻¹]` induced by the universal property
of localization. -/
noncomputable def cechMapFromG :
    Localization.Away g →+* Localization.Away (f * g) :=
  Localization.awayLift (algebraMap A (Localization.Away (f * g))) g
    (isUnit_algebraMap_of_away_mul_right A f g)

/-- The Čech differential `A[f⁻¹] × A[g⁻¹] → A[(fg)⁻¹]`, sending
`(s, t) ↦ s|_{D(fg)} - t|_{D(fg)}`. Its cokernel is `H¹` for the two-element cover. -/
noncomputable def cechDifferential :
    Localization.Away f × Localization.Away g → Localization.Away (f * g) :=
  fun p => cechMapFromF A f g p.1 - cechMapFromG A f g p.2

end SheafCondition
end SheafCohomology
