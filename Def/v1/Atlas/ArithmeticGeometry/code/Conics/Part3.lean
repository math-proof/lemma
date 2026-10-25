/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Conics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.HasseMinkowski
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HasseMinkowski
import Mathlib
import Theorem.v1.Atlas.ArithmeticGeometry.code.Conics.Part2
variable [Invertible (2 : K)]


section Theorem23

variable {K : Type*} [Field K]

/-- The diagonal conic as a subset of $\mathbb{P}^2(K)$: the projective points $[x : y : z]$ satisfying $ax^2 + by^2 + cz^2 = 0$. -/
def DiagConicSet (K : Type*) [Field K] (a b c : K) :
    Set (Projectivization K (Fin 3 → K)) :=
  { P | a * (P.rep 0) ^ 2 + b * (P.rep 1) ^ 2 + c * (P.rep 2) ^ 2 = 0 }

/-- The projectivized stereographic forward map $\mathbb{P}^1(K) \to \mathbb{P}^2(K)$ induced by `stereoForward`, using the quadratic homogeneity to descend to projective space. -/
noncomputable def stereoForwardProj (a b c x₀ y₀ z₀ : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0) (h2ne : (2 : K) ≠ 0)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0) :
    Projectivization K (Fin 2 → K) → Projectivization K (Fin 3 → K) :=
  Projectivization.lift
    (fun v => Projectivization.mk K
      (stereoForward a b x₀ y₀ z₀ (v.val 0) (v.val 1))
      (stereoForward_ne_zero a b c x₀ y₀ z₀ _ _ ha hb hc hz₀ h2ne hpt
        ((fin2_ne_zero_iff _).mp v.prop)))
    (by
      intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ t ht
      have hw : w₁ = t • w₂ := ht
      have h0 : w₁ 0 = t * w₂ 0 := by rw [hw]; simp [Pi.smul_apply, smul_eq_mul]
      have h1 : w₁ 1 = t * w₂ 1 := by rw [hw]; simp [Pi.smul_apply, smul_eq_mul]
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨t ^ 2, funext fun i => by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [h0, h1]
        exact (stereoForward_smul a b x₀ y₀ z₀ t (w₂ 0) (w₂ 1) i).symm⟩)

end Theorem23
