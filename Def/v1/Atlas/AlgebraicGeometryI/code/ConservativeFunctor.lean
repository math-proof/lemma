/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ConservativeFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.ConservativeFunctor
open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]


/-- A fully faithful left adjoint with a conservative right adjoint gives an equivalence of
categories. -/
noncomputable def adjunction_equivalence_of_fullyFaithful_conservative
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Full] [L.Faithful]
    [R.ReflectsIsomorphisms] : C ≌ D := by


  have : ∀ Y, IsIso (adj.counit.app Y) :=
    fun Y => isIso_of_reflects_iso (adj.counit.app Y) R

  exact adj.toEquivalence

