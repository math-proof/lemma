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
import Structure.v1.Atlas.Buildings.code.HeckeAlgebra.HeckeStructureTheorem
universe u


noncomputable section

open Module

section GoalTwentyFour

attribute [instance] BNPairOmegaContext.algH BNPairOmegaContext.ringH

namespace BNPairOmegaContext

variable {k : Type u} [CommRing k] {Ω : Type u} [Group Ω]

variable (ctx : BNPairOmegaContext k Ω)

/-- Packages `ch : Ω → H` as a monoid homomorphism. -/
def chMonoidHom : Ω →* ctx.H where
  toFun := ctx.ch
  map_one' := ctx.ch_one
  map_mul' σ τ := by rw [ctx.ch_mul]

/-- Induced $k$-algebra homomorphism $k[Ω] → H$ extending `chMonoidHom`. -/
def algHomOmega : MonoidAlgebra k Ω →ₐ[k] ctx.H :=
  MonoidAlgebra.lift k ctx.H Ω ctx.chMonoidHom

/-- The algebra isomorphism $k[Ω] ≃ₐ H_Ω$, where $H_Ω$ is the image subalgebra. -/
def HOmega_algEquiv : MonoidAlgebra k Ω ≃ₐ[k] (ctx.algHomOmega).range :=
  AlgEquiv.ofInjective ctx.algHomOmega ctx.algHomOmega_injective

end BNPairOmegaContext
end GoalTwentyFour
end
