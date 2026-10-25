/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Def.StatisticalMechanics.Code.SLE.Cardy.Part2
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

@[simp] lemma Mobius.id_apply {K : Type*} [Field K] (z : K) :
    (Mobius.id K).apply z = z := by simp [Mobius.apply, Mobius.id]


lemma crossRatio_translation_invariant {K : Type*} [Field K]
    (t z₁ z₂ z₃ z₄ : K) :
    crossRatio (z₁ + t) (z₂ + t) (z₃ + t) (z₄ + t) = crossRatio z₁ z₂ z₃ z₄ := by
  simp only [crossRatio]
  ring_nf


lemma crossRatio_scaling_invariant {K : Type*} [Field K]
    {s : K} (hs : s ≠ 0) (z₁ z₂ z₃ z₄ : K) :
    crossRatio (s * z₁) (s * z₂) (s * z₃) (s * z₄) = crossRatio z₁ z₂ z₃ z₄ := by
  simp only [crossRatio]
  rw [show s * z₁ - s * z₃ = s * (z₁ - z₃) by ring,
    show s * z₂ - s * z₄ = s * (z₂ - z₄) by ring,
    show s * z₁ - s * z₄ = s * (z₁ - z₄) by ring,
    show s * z₂ - s * z₃ = s * (z₂ - z₃) by ring]
  rw [mul_mul_mul_comm s (z₁ - z₃) s (z₂ - z₄),
    mul_mul_mul_comm s (z₁ - z₄) s (z₂ - z₃)]
  rw [mul_div_mul_left _ _ (mul_ne_zero hs hs)]


end StatMech.SLE
