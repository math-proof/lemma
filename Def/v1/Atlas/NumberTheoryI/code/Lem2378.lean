/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem2378.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

@[expose] public section

open CategoryTheory MonoidalCategory Limits

universe u

variable (R : Type u) [CommRing R]


noncomputable def lemma_23_78 (M A : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) 0).obj M).obj A ≅ M ⊗ A :=
  (Functor.leftDerivedZeroIsoSelf ((tensoringLeft (ModuleCat.{u} R)).obj M)).app A

