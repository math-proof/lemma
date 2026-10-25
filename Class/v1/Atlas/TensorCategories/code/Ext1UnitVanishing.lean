/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Ext1UnitVanishing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.HigherDerivation
import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity
import Instance.v1.Atlas.TensorCategories.code.HigherDerivation
import Def.v1.Atlas.TensorCategories.code.Ext1UnitVanishing
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits

universe v u w


noncomputable section

namespace TensorCategories

section Ext1Def

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A `k`-linear abelian monoidal category that has enough projectives and finite-
dimensional Hom spaces; this is the underlying ring-category structure used in EGNO. -/
class FiniteRingCategory (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    extends MonoidalCategory C, Abelian C, Linear k C where
  enoughProj : EnoughProjectives C
  homFiniteDim : ∀ (X Y : C), FiniteDimensional k (X ⟶ Y)

end Ext1Def
end TensorCategories
end
