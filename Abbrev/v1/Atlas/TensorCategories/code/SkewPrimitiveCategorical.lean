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
public import Def.v1.Atlas.TensorCategories.code.SkewPrimitiveCategorical.Part4
set_option maxHeartbeats 800000

open Coalgebra
open scoped TensorProduct
open CategoryTheory MonoidalCategory Category Limits

universe v u w


@[expose] public noncomputable section

section ComoduleExt

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

abbrev SkewQuot (g h : C) :=
  (skewPrimitiveSpace (R := k) g h) ⧸
    (Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
      (trivialSkewPrimitiveSubspace (k := k) g h))

end ComoduleExt
end
