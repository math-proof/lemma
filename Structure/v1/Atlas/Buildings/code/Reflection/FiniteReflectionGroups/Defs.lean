/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/FiniteReflectionGroups/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part4
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Finite.Basic
import Def.v1.Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Defs.Part2
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace FiniteReflectionGroups

/-- A (finite) root system in an inner product space: a nonempty finite set $Φ$ of nonzero
vectors that spans $E$ and is closed under reflection $s_α(β) ∈ Φ$ for all $α,β ∈ Φ$. -/
structure RootSystem (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  roots : Finset E
  roots_ne_zero : ∀ α ∈ roots, α ≠ 0
  roots_nonempty : roots.Nonempty
  reflection_closed : ∀ α ∈ roots, ∀ β ∈ roots, linearReflection α β ∈ roots
  roots_span : Submodule.span ℝ (roots : Set E) = ⊤

end FiniteReflectionGroups
end
