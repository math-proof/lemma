/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicGeometryI.code.DegreeAdditivity
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DegreeAdditivity
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GrothendieckGroup
import Def.v1.Atlas.AlgebraicGeometryI.code.GrothendieckGroup.Part3
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves
open scoped TensorProduct


section Saturation

variable {R : Type*} [CommRing R] [IsDomain R]

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Universal property of `K_0`: any short-exact-sequence-additive function `ModuleCat R → G`
lifts uniquely to a group homomorphism `K_0(R) →+ G`. -/
noncomputable def CoherentSheavesCurves.K0.lift (R : Type*) [Ring R]
    {G : Type*} [AddCommGroup G]
    (φ : ModuleCat R → G) (hφ : DegreeAdditivity.IsSESAdditive R φ) :
    CoherentSheavesCurves.K0 R →+ G :=
  DegreeAdditivity.GrothendieckGroupK0.lift R φ hφ

/-- Deprecated alias for `DegreeAdditivity.K0SESRelation`. -/
@[deprecated DegreeAdditivity.K0SESRelation (since := "2025-06-01")]
def CoherentSheavesCurves.SESRelation (R : Type*) [CommRing R] :=
  DegreeAdditivity.K0SESRelation R

end GrothendieckGroup

section Degree

variable {R : Type*} [Ring R]

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The degree of a module `M` over `R`, defined as the `R`-module length of `M` (a value in
`ℕ∞`). On curves this realizes the degree of a torsion coherent sheaf. -/
noncomputable def CoherentSheavesCurves.degree (R : Type*) [Ring R]
    (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R M

end Degree
