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
public import Abbrev.v1.Atlas.AlgebraicCombinatorics.code.YoungEigenvalues
set_option autoImplicit false


public noncomputable section

namespace YoungEigenvalues

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

structure YoungLatticeOps (i : ℕ) where
  U : PartitionSpace i →ₗ[ℝ] PartitionSpace (i + 1)
  D : PartitionSpace (i + 1) →ₗ[ℝ] PartitionSpace i
  hU_inj : Function.Injective U
  hD_surj : Function.Surjective D

structure YoungLatticeFamily where
  ops : (i : ℕ) → YoungLatticeOps i
  hcomm : ∀ (i : ℕ) (w : PartitionSpace (i + 1)),
    (ops (i + 1)).D ((ops (i + 1)).U w) = w + (ops i).U ((ops i).D w)
  hbase : (ops 0).D.comp (ops 0).U = LinearMap.id

end YoungEigenvalues
end
