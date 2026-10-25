/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularObject.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Def.v1.Atlas.TensorCategories.code.RegularObject


/-- Frobenius–Perron data for a finite tensor category: a nonempty finite
indexing type `I` of simple objects, together with the (strictly positive)
Frobenius–Perron dimensions of the simples and of their projective covers. -/
structure FiniteTensorCategoryFPData where
  I : Type*
  [I_fintype : Fintype I]
  [I_nonempty : Nonempty I]
  fpDimSimple : I → ℝ
  fpDimProjCover : I → ℝ
  fpDimSimple_pos : ∀ i : I, fpDimSimple i > 0
  fpDimProjCover_pos : ∀ i : I, fpDimProjCover i > 0

