/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.IntegralsDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.IntegralsDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.DistinguishedInvertible
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Instance.v1.Atlas.TensorCategories.code.DistinguishedInvertible.Part2
import Mathlib.RingTheory.SimpleModule.Basic
import Class.v1.Atlas.TensorCategories.code.IntegralsCartanMatrix
set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w


section CartanMatrix

variable {k : Type w} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The left quantum trace of a morphism `a : V ⟶ V**`, defined as the composition
`coev_V ≫ (a ▷ V*) ≫ ev_{V*}` ending in `𝟙_ C ⟶ 𝟙_ C`. -/
noncomputable def leftQuantumTrace' {V : C} (a : V ⟶ (Vᘁ)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ V (Vᘁ) ≫ (a ▷ Vᘁ) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ)

end CartanMatrix
