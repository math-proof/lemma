/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ConservativeFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.ConservativeFunctor

@[expose] public section

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

