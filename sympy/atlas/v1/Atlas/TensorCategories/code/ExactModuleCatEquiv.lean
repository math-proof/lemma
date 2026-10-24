/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCatEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.AlgebrasInCategories
import Lemma.Category.Atlas.v1.TensorCategories.code.AlgebrasInCategories
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.InternalHom
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.ExactModuleCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.InternalHom
import sympy.atlas.v1.Atlas.TensorCategories.code.FiniteTensorCategory
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option maxHeartbeats 800000

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]


/-- An algebra in `C` represented as a structure carrying both the underlying object
and the `MonObj` instance providing its algebra structure. -/
structure InternalEndAlgebra where
  carrier : C
  [monObj : MonObj carrier]

attribute [instance] InternalEndAlgebra.monObj

namespace InternalEndAlgebra

variable (A : InternalEndAlgebra (C := C))

/-- The multiplication morphism of the internal algebra. -/
noncomputable def mul : A.carrier ⊗ A.carrier ⟶ A.carrier := μ[A.carrier]

/-- The unit morphism of the internal algebra. -/
noncomputable def one : 𝟙_ C ⟶ A.carrier := η[A.carrier]

/-- Wrap an object `A : C` carrying a `MonObj` instance as an `InternalEndAlgebra`. -/
def ofMonObj (A : C) [MonObj A] : InternalEndAlgebra (C := C) where
  carrier := A

/-- The trivial internal algebra given by the monoidal unit `𝟙_ C`. -/
def ofUnit : InternalEndAlgebra (C := C) where
  carrier := 𝟙_ C

end InternalEndAlgebra

/-- The default internal algebra is the trivial one on `𝟙_ C`. -/
instance : Inhabited (InternalEndAlgebra (C := C)) where
  default := InternalEndAlgebra.ofUnit


/-- The data needed to set up the internal-Hom functor to right modules over an
internal algebra: a chosen generator `gen ∈ M`, the internal end algebra of `gen`, and
a functor `F` from `M` to right modules over that algebra. -/
class InternalHomData
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [LeftModuleCategory C M] where
  gen : M
  endAlgebra : InternalEndAlgebra (C := C)
  F : M ⥤ RightMod_ (A := endAlgebra.carrier)


variable {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]

/-- The biexactness property of the internal Hom bifunctor on an exact module category:
it preserves monos and epis on the right, and exchanges monos and epis on the left. -/
class InternalHomBiexact
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [ExactModuleCategory C M]
    [HasModuleInternalHom C M] : Prop where
  right_preserves_mono : ∀ (m₁ : M) {m₂ m₂' : M} (f : m₂ ⟶ m₂'),
    Mono f → Mono (moduleIHomMapRight (C := C) m₁ f)
  right_preserves_epi : ∀ (m₁ : M) {m₂ m₂' : M} (f : m₂ ⟶ m₂'),
    Epi f → Epi (moduleIHomMapRight (C := C) m₁ f)
  left_sends_mono_to_epi : ∀ {m₁ m₁' : M} (f : m₁ ⟶ m₁') (m₂ : M),
    Mono f → Epi (moduleIHomMapLeft (C := C) f m₂)
  left_sends_epi_to_mono : ∀ {m₁ m₁' : M} (f : m₁ ⟶ m₁') (m₂ : M),
    Epi f → Mono (moduleIHomMapLeft (C := C) f m₂)

/-- Internal Hom is biexact in any exact module category equipped with internal Homs. -/
class InternalHomExact
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [LeftModuleCategory C M]
    [hom : InternalHomData C M] : Prop where
  preservesEpi : ∀ {N₁ N₂ : M} (f : N₁ ⟶ N₂), Epi f → Epi (hom.F.map f)

/-- The chosen generator `gen` generates the module category: every `N ∈ M` admits an
epimorphism from `X ⊗ gen` for some `X ∈ C`. -/
class InternalHomGeneration
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [LeftModuleCategory C M]
    [hom : InternalHomData C M] : Prop where
  generation : ∀ (N : M), ∃ (X : C) (f : X ⊗ᵐ hom.gen ⟶ N), Epi f


/-- Faithfulness of the internal-Hom functor `F : M ⥤ RightMod (endAlgebra)`. -/
class InternalHomFaithful
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [LeftModuleCategory C M]
    [hom : InternalHomData C M] : Prop where
  faithful : hom.F.Faithful

/-- Fullness of the internal-Hom functor `F : M ⥤ RightMod (endAlgebra)`. -/
class InternalHomFull
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [LeftModuleCategory C M]
    [hom : InternalHomData C M] : Prop where
  full : hom.F.Full

/-- Essential surjectivity of the internal-Hom functor
`F : M ⥤ RightMod (endAlgebra)`. -/
class InternalHomEssSurj
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [LeftModuleCategory C M]
    [hom : InternalHomData C M] : Prop where
  essSurj : hom.F.EssSurj


/-- If the internal-Hom functor `F` is exact and the chosen generator generates `M`,
then `F` is faithful. -/
noncomputable def internalHomEquivalence_of_steps
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [LeftModuleCategory C M]
    [hom : InternalHomData C M]
    [hFaith : InternalHomFaithful C M]
    [hFull : InternalHomFull C M]
    [hEss : InternalHomEssSurj C M] :
    M ≌ RightMod_ (A := hom.endAlgebra.carrier) := by
  haveI := hFaith.faithful
  haveI := hFull.full
  haveI := hEss.essSurj
  haveI : hom.F.IsEquivalence := { faithful := ‹_›, full := ‹_›, essSurj := ‹_› }
  exact hom.F.asEquivalence

/-- The internal end algebra produced by the `InternalHomData` package. -/
class ExactModCatInternalHom
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [ExactModuleCategory C M] extends
    InternalHomData C M,
    InternalHomExact C M,
    InternalHomGeneration C M

/-- Theorem (EGNO, Section 2.11): An exact module category equipped with an internal
end algebra and the relevant exactness/generation conditions is equivalent to right
modules over that algebra. -/
class IsIndecomposableModuleCategoryBasic
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] : Prop where
  nonempty : Nonempty M
  indecomposable : True


/-- Specialization of `exact_module_cat_equiv` to the indecomposable case. -/
class HasProjectiveGenerator
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [ExactModuleCategory C M] extends
    ExactModCatInternalHom C M


/-- Specialization of `exact_module_cat_equiv` to exact module categories over a finite
tensor category that admit a projective generator. -/
noncomputable def algebra_determines_module_cat
    (A : C) [MonObj A]
    {M₁ : Type u₂} [Category.{v₂} M₁]
    {M₂ : Type u₂} [Category.{v₂} M₂]
    (e₁ : M₁ ≌ RightMod_ (A := A))
    (e₂ : M₂ ≌ RightMod_ (A := A)) :
    M₁ ≌ M₂ :=
  e₁.trans e₂.symm

end CategoryTheory
