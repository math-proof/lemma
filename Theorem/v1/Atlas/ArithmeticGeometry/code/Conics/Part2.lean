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
import Def.v1.Atlas.ArithmeticGeometry.code.Conics.Part2
variable [Invertible (2 : K)]


section Theorem23

variable {K : Type*} [Field K]

/-- A function $v : \mathrm{Fin}\,2 \to K$ is nonzero iff not both coordinates $v(0), v(1)$ are zero. -/
lemma fin2_ne_zero_iff {K : Type*} [Field K] (v : Fin 2 → K) :
    v ≠ 0 ↔ ¬(v 0 = 0 ∧ v 1 = 0) := by
  constructor
  · intro hv ⟨h0, h1⟩; apply hv; ext i; fin_cases i <;> assumption
  · intro hv h; apply hv; exact ⟨by rw [h]; rfl, by rw [h]; rfl⟩


/-- The stereographic forward map sends any nonzero $(U, V)$ to a nonzero point of $K^3$. This is needed to descend the map to projective space. -/
theorem stereoForward_ne_zero (a b c x₀ y₀ z₀ U V : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (h2ne : (2 : K) ≠ 0)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0)
    (hUV : ¬(U = 0 ∧ V = 0)) :
    stereoForward a b x₀ y₀ z₀ U V ≠ 0 := by
  intro h
  have h0 : stereoForward a b x₀ y₀ z₀ U V 0 = 0 := by rw [h]; rfl
  have h2 : stereoForward a b x₀ y₀ z₀ U V 2 = 0 := by rw [h]; rfl
  simp only [stereoForward] at h0 h2
  have haUbV : a * U ^ 2 + b * V ^ 2 = 0 := by
    have : z₀ * (a * U ^ 2 + b * V ^ 2) = 0 := by linear_combination -h2
    exact (mul_eq_zero.mp this).resolve_left hz₀
  have key : 2 * b * V * (y₀ * U - x₀ * V) = 0 := by linear_combination h0 - x₀ * haUbV
  have h2bne : (2 : K) * b ≠ 0 := mul_ne_zero h2ne hb
  have hsum_ne : a * x₀ ^ 2 + b * y₀ ^ 2 ≠ 0 := by
    intro hsum
    have : c * z₀ ^ 2 = 0 := by linear_combination hpt - hsum
    exact mul_ne_zero hc (pow_ne_zero _ hz₀) this
  rcases mul_eq_zero.mp key with h2bV | hyx
  · rcases mul_eq_zero.mp h2bV with h2b_bad | hV
    · exact absurd h2b_bad h2bne
    · have hU : U = 0 := by
        have : a * U ^ 2 = 0 := by
          rw [hV, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] at haUbV; exact haUbV
        exact (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp ((mul_eq_zero.mp this).resolve_left ha)
      exact hUV ⟨hU, hV⟩
  · have hyx_eq : y₀ * U = x₀ * V := sub_eq_zero.mp hyx
    have hkey : U ^ 2 * (a * x₀ ^ 2 + b * y₀ ^ 2) = 0 := by
      have : U ^ 2 * (a * x₀ ^ 2 + b * y₀ ^ 2) =
        x₀ ^ 2 * (a * U ^ 2 + b * V ^ 2) +
          b * (y₀ * U - x₀ * V) * (y₀ * U + x₀ * V) := by ring
      rw [this, haUbV, show y₀ * U - x₀ * V = 0 from sub_eq_zero.mpr hyx_eq]; ring
    rcases mul_eq_zero.mp hkey with hU2 | hsum
    · have hU : U = 0 := (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp hU2
      have hV : V = 0 := by
        rw [hU, mul_zero] at hyx_eq
        rcases mul_eq_zero.mp hyx_eq.symm with hx | hV
        · have : b * V ^ 2 = 0 := by
            rw [hU, zero_pow (by omega : 2 ≠ 0), mul_zero, zero_add] at haUbV; exact haUbV
          exact (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp ((mul_eq_zero.mp this).resolve_left hb)
        · exact hV
      exact hUV ⟨hU, hV⟩
    · exact absurd hsum hsum_ne

end Theorem23
