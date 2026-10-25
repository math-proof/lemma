/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Theorem.StatisticalMechanics.Code.SLE.Cardy.Part8
import Def.StatisticalMechanics.Code.SLE.CardyCLE.Part2
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

@[simp] lemma discRiemannMap_apply (z : ℂ) (r : ℝ) (w : ℂ) :
    discRiemannMap z r w = z + (r : ℂ) * w := rfl


@[simp] lemma discRiemannMap_zero (z : ℂ) (r : ℝ) : discRiemannMap z r 0 = z := by
  simp [discRiemannMap]


lemma hasDerivAt_discRiemannMap (z : ℂ) (r : ℝ) :
    HasDerivAt (discRiemannMap z r) (r : ℂ) 0 := by
  unfold discRiemannMap
  have h : HasDerivAt (fun w : ℂ => z + (r : ℂ) * w) ((r : ℂ) * 1) 0 :=
    ((hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)).const_add z
  simpa using h


lemma hasConformalRadius_disc (z : ℂ) {r : ℝ} (hr : 0 < r) :
    HasConformalRadius z (discRiemannMap z r) r :=
  ⟨discRiemannMap_zero z r, hasDerivAt_discRiemannMap z r, hr⟩


lemma HasConformalRadius.pos {z : ℂ} {φ : ℂ → ℂ} {r : ℝ}
    (h : HasConformalRadius z φ r) : 0 < r := h.2.2


lemma HasConformalRadius.map_zero {z : ℂ} {φ : ℂ → ℂ} {r : ℝ}
    (h : HasConformalRadius z φ r) : φ 0 = z := h.1


lemma HasConformalRadius.unique {z : ℂ} {φ : ℂ → ℂ} {r₁ r₂ : ℝ}
    (h₁ : HasConformalRadius z φ r₁) (h₂ : HasConformalRadius z φ r₂) : r₁ = r₂ := by
  have := h₁.2.1.unique h₂.2.1
  exact_mod_cast this


lemma discConformalRadius_strictMono : StrictMono discConformalRadius :=
  strictMono_id


lemma discConformalRadius_mono : Monotone discConformalRadius :=
  monotone_id


lemma discConformalRadius_pos {r : ℝ} (hr : 0 < r) : 0 < discConformalRadius r := hr


end StatMech.SLE
