/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/HeckeStructureTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
universe u


public noncomputable section

open Module

section GoalTwentyFour

/-- Context for the $H_Ω ≃ k[Ω]$ structure result: an algebra $H$ over $k$ together
with a $k$-linearly independent monoid homomorphism `ch : Ω → H`. -/
structure BNPairOmegaContext (k : Type u) [CommRing k] (Ω : Type u) [Group Ω] where
  H : Type u
  [ringH : Ring H]
  [algH : Algebra k H]
  ch : Ω → H
  ch_mul : ∀ σ τ : Ω, ch σ * ch τ = ch (σ * τ)
  ch_one : ch 1 = (1 : H)
  ch_linearIndependent : LinearIndependent k ch

end GoalTwentyFour
end
