/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Class.v1.Atlas.TensorCategories.code.SkewPrimitiveCategorical

@[expose] public section

set_option maxHeartbeats 800000

open Coalgebra
open scoped TensorProduct
open CategoryTheory MonoidalCategory Category Limits

universe v u w


noncomputable section

section TrivialSkewPrimitive

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- The one-dimensional subspace spanned by the trivial skew-primitive element `h - g`. -/
def trivialSkewPrimitiveSubspace (g h : C) : Submodule k C :=
  Submodule.span k {h - g}

/-- The reduced space of skew-primitives: the quotient of `skewPrimitiveSpace g h` by its trivial
sub-line, capturing genuinely nontrivial skew-primitive directions. -/
def reducedSkewPrimitiveSpace
    {g h : C} (_hg : IsGrouplike (R := k) g) (_hh : IsGrouplike (R := k) h) :
    Type u :=
  (skewPrimitiveSpace (R := k) g h) ⧸
    (Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
      (trivialSkewPrimitiveSubspace (k := k) g h))

end TrivialSkewPrimitive
end
