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
import Def.v1.Atlas.Buildings.code.HeckeAlgebra.HeckeStructureTheorem
universe u


noncomputable section

open Module

section GoalTwentyThree

/-- Full BN-pair context recording the data needed for the generalized Hecke-algebra
structure theorem $H ≅ k[Ω] ⊗ H_o$: characters of $Ω$ and $W$, an inclusion $H_o → H$,
a joint basis indexed by $Ω × W$, and the conjugation action `omegaConj`. -/
structure FullBNPairContext (k : Type u) [CommRing k] (Ω : Type u) [Group Ω]
    (W : Type u) [Group W] where
  H : Type u
  [ringH : Ring H]
  [algH : Algebra k H]
  H_o : Type u
  [ringHo : Ring H_o]
  [algHo : Algebra k H_o]
  ch : Ω → H
  ch_o : W → H_o
  incl : H_o →ₐ[k] H
  ch_full : Ω × W → H
  H_basis : Basis (Ω × W) k H
  H_basis_eq : ∀ σw : Ω × W, H_basis σw = ch_full σw
  ch_full_one : ∀ σ : Ω, ch_full (σ, 1) = ch σ
  ch_full_incl : ∀ w : W, ch_full (1, w) = incl (ch_o w)
  omegaConj : Ω → W → W
  omegaConj_one : ∀ w : W, omegaConj 1 w = w
  omegaConj_mul : ∀ σ τ : Ω, ∀ w : W,
    omegaConj (σ * τ) w = omegaConj τ (omegaConj σ w)
  omegaConj_action_one : ∀ σ : Ω, omegaConj σ 1 = 1
  omegaConj_action_mul : ∀ σ : Ω, ∀ w w' : W,
    omegaConj σ (w * w') = omegaConj σ w * omegaConj σ w'
  ch_mul_omega : ∀ σ τ : Ω, ch σ * ch τ = ch (σ * τ)
  incl_mul : ∀ a b : H_o, incl (a * b) = incl a * incl b
  ch_one : ch 1 = (1 : H)
  ch_o_one : ch_o 1 = (1 : H_o)
  incl_one : incl 1 = (1 : H)

end GoalTwentyThree
end
