/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohLocalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Flat.Localization
import Mathlib.AlgebraicGeometry.Modules.Tilde
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec14QCohProjective
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.Lec14QCohProjective

namespace QCohLocalization

open LocalizedModule

/-- The localized module `M_f := S^{-1} M` at the powers of `f`, encoding the
value `Γ(D(f), M̃)` of the tilde sheaf on a principal open. -/
abbrev ModuleTilde (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (f : R) : Type _ :=
  LocalizedModule (Submonoid.powers f) M

/-- Every quasi-coherent sheaf on `Spec R` lies in the essential image of the
tilde functor (the Thm 12.1 direction). -/
noncomputable def tildeSpec_globalSectionsModule (F : (Spec R).Modules) :
    ModuleCat.{u} R :=
  moduleSpecΓFunctor.obj F

/-- The unit of the `tilde ⊣ Γ` adjunction is an isomorphism, expressing
the identity `Γ(M̃) ≅ M`. -/
instance tildeSpec_unitIso : IsIso (tilde.adjunction (R := R)).unit :=
  inferInstance

/-- The sheaf `M̃` on `Spec R` is quasi-coherent for any `R`-module `M`. -/
instance tildeSpec_isQuasicoherent (M : ModuleCat.{u} R) :
    (tilde M).IsQuasicoherent :=
  inferInstance

section Prop20Projective

open AlgebraicGeometry CategoryTheory

universe v

variable {A : Type v} [CommRing A] {σ : Type v} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

end Prop20Projective
