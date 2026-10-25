/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FPdimProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Def.v1.Atlas.TensorCategories.code.FPdimProps.Part2
set_option maxHeartbeats 800000


namespace CategoryTheory

open CategoryTheory MonoidalCategory Limits

attribute [reducible, instance] FiniteMultitensorDecompData.instFintype
  FiniteMultitensorDecompData.instDecEq

/-- Numerical data of the Frobenius–Perron dimensions of simples and
projective covers in a finite tensor category, together with the
dual involution and the identity `FPdim(P_i)·FPdim(X_{i*}) = FPdim(C)`
from EGNO §1.47. -/
structure FiniteTensorCategoryFPdimData where
  I : Type*
  [instFintype : Fintype I]
  [instDecEq : DecidableEq I]
  [instNonempty : Nonempty I]
  fpDimSimple : I → ℝ
  fpDimProjCover : I → ℝ
  dualIndex : I → I
  fpDimSimple_pos : ∀ i, fpDimSimple i > 0
  fpDimProjCover_pos : ∀ i, fpDimProjCover i > 0
  fpDim_projCover_eq : ∀ i,
    fpDimProjCover i * fpDimSimple (dualIndex i) =
      ∑ j : I, fpDimSimple j * fpDimProjCover j

end CategoryTheory
