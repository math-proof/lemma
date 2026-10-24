/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyComposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.GeometricAlgebra.OppositeConjugacyProof
import Lemma.Fin.Len
import Lemma.Fin.IsCompl
import sympy.atlas.v1.Atlas.Buildings.code.GeometricAlgebra.SemidirectExistence

namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Inductive invariant for the composition of swap automorphisms used to conjugate one
opposite flag to another. After `levels_done` swap steps, the automorphism `e` is required
to stabilize every level of the fixed flag `F` and to have already mapped the top
`levels_done` levels of `F'₁` onto the corresponding levels of `F'₂`. -/
structure SwapCompositionInvariant (F F'₁ F'₂ : Flag k V)
    (h₁ : Flag.isOppositeFlag F F'₁) (h₂ : Flag.isOppositeFlag F F'₂)
    (e : V ≃ₗ[k] V) (levels_done : ℕ) : Prop where
  preserves_F : ∀ i : Fin F.len, (F.spaces i).map e.toLinearMap = F.spaces i
  maps_F'_done : ∀ j : Fin F'₁.len,
    let j₂ : Fin F'₂.len := ⟨j.val, by have := opposite_flags_same_len F F'₁ F'₂ h₁ h₂; omega⟩
    j.val ≥ F'₁.len - levels_done →
    (F'₁.spaces j).map e.toLinearMap = F'₂.spaces j₂

/-- Inductive-step hypothesis packaging the existence of a swap that advances the
`SwapCompositionInvariant` from `levels_done` to `levels_done + 1`, for every choice of
flags and prior approximation `e_prev`. This is the key local construction supplied by
`stepHyp_proof`. -/
structure SwapCompositionStepHyp (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] : Prop where
  step : ∀ (F F'₁ F'₂ : Flag k V)
    (h₁ : Flag.isOppositeFlag F F'₁) (h₂ : Flag.isOppositeFlag F F'₂)
    (levels_done : ℕ) (h_lt : levels_done < F'₁.len)
    (e_prev : V ≃ₗ[k] V)
    (inv : SwapCompositionInvariant F F'₁ F'₂ h₁ h₂ e_prev levels_done),
    ∃ e_next : V ≃ₗ[k] V,
      SwapCompositionInvariant F F'₁ F'₂ h₁ h₂ e_next (levels_done + 1)
