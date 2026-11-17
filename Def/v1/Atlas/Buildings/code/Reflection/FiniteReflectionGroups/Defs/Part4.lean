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
public import Inductive.v1.Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Defs

@[expose] public section

open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace FiniteReflectionGroups

variable {Φ : RootSystem E}

/-- The underlying set of the Weyl group inside $E → E$. -/
def RootSystem.weylGroupSet (Φ : RootSystem E) : Set (E → E) :=
  { g | Φ.WeylGroupMem g }

end FiniteReflectionGroups
end
