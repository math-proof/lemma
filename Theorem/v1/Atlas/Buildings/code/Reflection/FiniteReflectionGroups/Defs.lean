/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/FiniteReflectionGroups/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part4
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Set.Finite.Basic
public import Def.v1.Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Defs
open scoped InnerProductSpace
open Set

public section

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace FiniteReflectionGroups

/-- Unfolding lemma for linearReflectionLM. -/
@[simp] theorem linearReflectionLM_apply (a v : E) :
    linearReflectionLM a v = linearReflection a v := rfl

end FiniteReflectionGroups
end
