/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LMWY.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.LMWY.Part2
open Matrix


namespace HomogeneousDynamics

/-- A proper homogeneous subspace of $SL(3,\mathbb{R}) / SL(3,\mathbb{Z})$: a closed proper
subset invariant under a nontrivial proper subgroup of $SL(3,\mathbb{R})$.  These are the
exceptional sets near which the unipotent orbit can fail to equidistribute. -/
structure ProperHomogeneousSubspace
    [TopologicalSpace (SpecialLinearGroup (Fin 3) ℝ ⧸ SL3Z)] where
  carrier : Set (SpecialLinearGroup (Fin 3) ℝ ⧸ SL3Z)
  isClosed : IsClosed carrier
  isProper : carrier ≠ Set.univ
  isSubgroupInvariant : ∃ H : Subgroup (SpecialLinearGroup (Fin 3) ℝ),
    H ≠ ⊤ ∧ ∀ (h : SpecialLinearGroup (Fin 3) ℝ), h ∈ H → ∀ y ∈ carrier, h • y ∈ carrier

end HomogeneousDynamics
