/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

namespace SheafCohomology

section SheafCondition

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- The "restriction to the cover" map for an `A`-module `M`: it sends `m` to the
pair of its images in the localizations away from `f` and from `g`. This is the
first map of the Čech complex for the two-element cover `{D(f), D(g)}`. -/
noncomputable def locProductMap (f g : A) :
    M →ₗ[A] LocalizedModule (Submonoid.powers f) M × LocalizedModule (Submonoid.powers g) M :=
  LinearMap.prod
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)

end SheafCondition
end SheafCohomology
