/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohAffineEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace Proposition18

/-- The category of quasi-coherent sheaves of modules on a scheme `X`, realized
as the full subcategory of `X.Modules` cut out by the quasi-coherence property. -/
abbrev Scheme.Qcoh (X : Scheme.{u}) :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory

/-- Inclusion of quasi-coherent sheaves on `X` into all sheaves of modules on `X`. -/
def Scheme.Qcoh.incl (X : Scheme.{u}) : Scheme.Qcoh X ⥤ X.Modules :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι

/-- The tilde functor `M ↦ M̃` viewed with codomain the quasi-coherent subcategory
of `(Spec R).Modules`; sends an `R`-module to the associated quasi-coherent sheaf
on `Spec R`. -/
def tildeFunctorToQcoh (R : CommRingCat.{u}) : ModuleCat.{u} R ⥤ Scheme.Qcoh (Spec R) where
  obj M := ⟨tilde M, inferInstance⟩
  map f := ObjectProperty.homMk (tilde.map f)

/-- The tilde functor `Mod R → (Spec R).Modules` is fully faithful, the
fundamental input to Thm 11.1 / Thm 12.1. -/
def tilde_fullyFaithful (R : CommRingCat.{u}) :
    (tilde.functor R).FullyFaithful :=
  tilde.fullyFaithfulFunctor

/-- The adjunction `tilde ⊣ Γ` between the tilde functor and the global-sections
functor, one half of the equivalence `Mod R ≃ QCoh(Spec R)`. -/
def tildeGammaAdj (R : CommRingCat.{u}) :
    tilde.functor R ⊣ moduleSpecΓFunctor :=
  tilde.adjunction

/-- `tildeFunctorToQcoh R` is full: every map between tilde sheaves comes from
a module map, lifted from fullness of the underlying tilde functor. -/
instance tildeFunctorToQcoh_full (R : CommRingCat.{u}) : (tildeFunctorToQcoh R).Full where
  map_surjective {M N} f := by
    refine ⟨(tilde.functor R).preimage f.hom, ?_⟩
    apply ObjectProperty.hom_ext
    exact (tilde.functor R).map_preimage f.hom

/-- `tildeFunctorToQcoh R` is faithful: two `R`-module maps with equal tilde
images coincide. -/
instance tildeFunctorToQcoh_faithful (R : CommRingCat.{u}) :
    (tildeFunctorToQcoh R).Faithful where
  map_injective {M N f g} h := by
    have := congr_arg InducedCategory.Hom.hom h
    dsimp [tildeFunctorToQcoh] at this
    exact (tilde.functor R).map_injective this

set_option backward.isDefEq.respectTransparency false in


/-- Converse direction (Thm 12.1): every quasi-coherent sheaf on `Spec R`
arises (up to isomorphism) as `M̃` for some `R`-module `M`. -/
def qcoh_spec_equiv_moduleCat (R : CommRingCat.{u}) :
    ModuleCat.{u} R ≌ Scheme.Qcoh (Spec R) :=
  (tildeFunctorToQcoh R).asEquivalence


/-- Lem 24 (Lec 12): the pushforward `f_*` along an affine morphism preserves
quasi-coherent sheaves. -/
end Proposition18
