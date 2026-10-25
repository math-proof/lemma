/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/FiniteReflectionGroups/Theorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Defs.Part4
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace FiniteReflectionGroups

open Classical in
/-- Restriction of an endomorphism $g$ of $E$ to the finite set $Φ$ of roots, falling
back to the identity when $g$ does not preserve roots. -/
def restrictToRoots (Φ : RootSystem E) (g : E → E) : ↥Φ.roots → ↥Φ.roots :=
  fun ⟨β, hβ⟩ => if h : g β ∈ Φ.roots then ⟨g β, h⟩ else ⟨β, hβ⟩

end FiniteReflectionGroups
end
