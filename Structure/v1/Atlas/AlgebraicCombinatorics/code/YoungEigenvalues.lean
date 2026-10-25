/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungEigenvalues.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungTableaux
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungTableaux
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Real.Sqrt
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Abbrev.v1.Atlas.AlgebraicCombinatorics.code.YoungEigenvalues
set_option autoImplicit false


noncomputable section

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
