/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/HeckeStructureTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Structure.v1.Atlas.Buildings.code.HeckeAlgebra.HeckeStructureTheorem.Part2
universe u


noncomputable section

open Module

section GoalTwentyThree

attribute [instance] FullBNPairContext.algH FullBNPairContext.ringH
  FullBNPairContext.algHo FullBNPairContext.ringHo


namespace FullBNPairContext

variable {k : Type u} [CommRing k] {Ω : Type u} [Group Ω] {W : Type u} [Group W]

variable (ctx : FullBNPairContext k Ω W)


/-- Joint-basis factorization: $T_{(σ,w)} = \mathrm{ch}_Ω(σ) · \iota(\mathrm{ch}_o(w))$. -/
def structureIso : ctx.H ≃ₗ[k] (Ω × W →₀ k) :=
  ctx.H_basis.repr

end FullBNPairContext
end GoalTwentyThree
end
