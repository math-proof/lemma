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
set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w


section CartanMatrix

variable {k : Type w} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reinterpret a `ℕ`-valued Cartan matrix `C_mat` as a matrix over the field `k`
by casting each entry to `k`. -/
def cartanMatrixOverField (C_mat : ι → ι → ℕ) : Matrix ι ι k :=
  Matrix.of (fun i j => (C_mat i j : k))

end CartanMatrix
