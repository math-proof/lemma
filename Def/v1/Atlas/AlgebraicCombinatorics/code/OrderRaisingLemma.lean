/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrderRaisingLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty.Part2
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.SpernerProperty
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

namespace SpernerProperty

def IsOrderRaisingLinearMap {α β : Type*} [DecidableEq α]
    (U : (α → ℝ) →ₗ[ℝ] (β → ℝ)) (r : α → β → Prop) : Prop :=
  ∀ (x : α) (y : β), U (Pi.single x 1) y ≠ 0 → r x y

end SpernerProperty
