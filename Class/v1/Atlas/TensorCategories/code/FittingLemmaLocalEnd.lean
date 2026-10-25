/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FittingLemmaLocalEnd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Endomorphism
import Def.v1.Atlas.TensorCategories.code.FittingLemmaLocalEnd
set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u w


namespace CategoryTheory

/-- A `k`-linear abelian category satisfies the Fitting property if every indecomposable
object has a local endomorphism ring. This holds in finite abelian categories. -/
class FiniteAbelianCategory.HasLocalEndOfIndecomposable
    (k : Type w) [Field k] (C : Type u) [Category.{v} C] [Abelian C] [Linear k C] : Prop where
  isLocalRing_end_of_indecomposable :
    ∀ (P : C), Indecomposable P → IsLocalRing (End P)

end CategoryTheory
