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
import Def.v1.Atlas.TensorCategories.code.SkewPrimitiveCategorical
set_option maxHeartbeats 800000

open Coalgebra
open scoped TensorProduct
open CategoryTheory MonoidalCategory Category Limits

universe v u w


noncomputable section

namespace TensorCategories

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A finite `k`-linear ring category: an abelian monoidal `k`-linear category that has enough
projectives and finite-dimensional Hom-spaces. -/
class FiniteRingCategory (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    extends MonoidalCategory C, Abelian C, Linear k C where
  enoughProj : EnoughProjectives C
  homFiniteDim : ∀ (X Y : C), FiniteDimensional k (X ⟶ Y)

end TensorCategories
end
