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
import Def.v1.Atlas.TensorCategories.code.SkewPrimitiveCategorical.Part5
set_option maxHeartbeats 800000

open Coalgebra
open scoped TensorProduct
open CategoryTheory MonoidalCategory Category Limits

universe v u w


noncomputable section

section ComoduleExt

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- Additive group structure on `ComoduleExt1` transported from the reduced skew-primitive
quotient. -/
noncomputable instance ComoduleExt1.instAddCommGroup {g h : C} :
    AddCommGroup (ComoduleExt1 (k := k) g h) :=
  (ext1EquivSkewQuot (k := k)).addCommGroup

/-- `k`-module structure on `ComoduleExt1` transported from the reduced skew-primitive quotient. -/
noncomputable instance ComoduleExt1.instModule {g h : C} :
    Module k (ComoduleExt1 (k := k) g h) :=
  Equiv.module k (ext1EquivSkewQuot (k := k))

end ComoduleExt
end
