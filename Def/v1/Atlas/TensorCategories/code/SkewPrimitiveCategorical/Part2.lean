/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Class.v1.Atlas.TensorCategories.code.SkewPrimitiveCategorical
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
