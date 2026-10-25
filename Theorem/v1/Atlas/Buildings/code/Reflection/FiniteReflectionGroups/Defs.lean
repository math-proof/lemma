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
import Def.v1.Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Defs
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace FiniteReflectionGroups

/-- Unfolding lemma for linearReflectionLM. -/
@[simp] theorem linearReflectionLM_apply (a v : E) :
    linearReflectionLM a v = linearReflection a v := rfl

end FiniteReflectionGroups
end
