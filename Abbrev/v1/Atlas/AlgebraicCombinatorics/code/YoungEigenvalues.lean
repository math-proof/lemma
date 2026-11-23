/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungEigenvalues.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungTableaux
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungTableaux
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungEigenvalues
set_option autoImplicit false


@[expose] public noncomputable section

namespace YoungEigenvalues

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

abbrev PartitionSpace (j : ℕ) := Nat.Partition j →₀ ℝ

end YoungEigenvalues
end
