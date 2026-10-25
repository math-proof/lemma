/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Def.v1.Atlas.DifferentialAnalysis.code.JordanDecomposition.Part3


namespace ContinuousFunctions

open ContinuousLinearMap

section PosPartConstruction

variable {X : Type*} [MetricSpace X]

/-- For nonnegative `f`, the positive-part supremum is nonnegative. -/
lemma posPartSup_nonneg (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ posPartSup u f := by
  exact le_csSup (posPartSet_bddAbove u f hf)
    ⟨0, fun _ => le_refl 0, hf, by simp [map_zero]⟩

/-- The positive-part supremum is bounded above by `‖u‖ * ‖f‖`. -/
lemma posPartSup_le_norm_mul (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (hf : ∀ x, 0 ≤ f x) :
    posPartSup u f ≤ ‖u‖ * ‖f‖ := by
  exact csSup_le (posPartSet_nonempty u f hf) (fun r ⟨g, hg0, hgf, hr⟩ => by
    rw [hr]
    calc u g ≤ |u g| := le_abs_self _
      _ = ‖u g‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖u‖ * ‖g‖ := le_opNorm u g
      _ ≤ ‖u‖ * ‖f‖ :=
          mul_le_mul_of_nonneg_left (c0_norm_le_of_nonneg_le f g hg0 hgf) (norm_nonneg u))

/-- The positive-part supremum vanishes at the zero function. -/
lemma posPartSup_zero (u : C₀Map X →L[ℝ] ℝ) :
    posPartSup u 0 = 0 := by
  unfold posPartSup
  have h_set : posPartSet u 0 = {0} := by
    ext r; simp only [posPartSet, Set.mem_setOf_eq, Set.mem_singleton_iff]; constructor
    · rintro ⟨g, hg0, hg0', rfl⟩
      have : g = 0 := DFunLike.ext g 0 (fun x => by
        have h1 := hg0 x; have h2 := hg0' x
        simp only [ZeroAtInftyContinuousMap.coe_zero, Pi.zero_apply] at h2 ⊢; linarith)
      rw [this, map_zero]
    · rintro rfl
      exact ⟨0, fun _ => le_refl 0, fun _ => le_refl _, by simp [map_zero]⟩
  rw [h_set, csSup_singleton]

/-- Additivity of the positive-part supremum on nonnegative functions: for `f₁, f₂ ≥ 0` we have
`posPartSup u (f₁ + f₂) = posPartSup u f₁ + posPartSup u f₂`. -/
lemma posPartSup_add (u : C₀Map X →L[ℝ] ℝ) (f₁ f₂ : C₀Map X)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x) :
    posPartSup u (f₁ + f₂) = posPartSup u f₁ + posPartSup u f₂ := by
  unfold posPartSup
  apply le_antisymm
  ·
    apply csSup_le (posPartSet_nonempty u (f₁ + f₂) (fun x => add_nonneg (hf₁ x) (hf₂ x)))
    intro r ⟨g, hg0, hgf, hr⟩; rw [hr]
    set g₁ := c0min g f₁
    set g₂ := g - g₁
    have hg₁_0 : ∀ x, 0 ≤ g₁ x := fun x => le_min (hg0 x) (hf₁ x)
    have hg₁_f₁ : ∀ x, g₁ x ≤ f₁ x := fun x => min_le_right _ _
    have hg₂_0 : ∀ x, 0 ≤ g₂ x := fun x =>
      show g x - min (g x) (f₁ x) ≥ 0 from sub_nonneg.mpr (min_le_left _ _)
    have hg₂_f₂ : ∀ x, g₂ x ≤ f₂ x := fun x => by
      show g x - min (g x) (f₁ x) ≤ f₂ x
      have hgfx : g x ≤ f₁ x + f₂ x := hgf x
      rcases le_or_gt (g x) (f₁ x) with h | h
      · simp only [min_eq_left h]; linarith [hf₂ x]
      · simp only [min_eq_right (le_of_lt h)]; linarith
    have hg_eq : u g = u g₁ + u g₂ := by
      have : g = g₁ + g₂ := by
        ext x; show g x = min (g x) (f₁ x) + (g x - min (g x) (f₁ x)); ring
      rw [this, map_add]
    rw [hg_eq]
    exact add_le_add
      (le_csSup (posPartSet_bddAbove u f₁ hf₁) ⟨g₁, hg₁_0, hg₁_f₁, rfl⟩)
      (le_csSup (posPartSet_bddAbove u f₂ hf₂) ⟨g₂, hg₂_0, hg₂_f₂, rfl⟩)
  ·
    rw [← csSup_add (posPartSet_nonempty u f₁ hf₁) (posPartSet_bddAbove u f₁ hf₁)
                     (posPartSet_nonempty u f₂ hf₂) (posPartSet_bddAbove u f₂ hf₂)]
    apply csSup_le_csSup
      (posPartSet_bddAbove u (f₁ + f₂) (fun x => add_nonneg (hf₁ x) (hf₂ x)))
      ((posPartSet_nonempty u f₁ hf₁).add (posPartSet_nonempty u f₂ hf₂))
    intro r hr
    rw [Set.mem_add] at hr
    obtain ⟨r₁, hr₁, r₂, hr₂, hrr⟩ := hr
    obtain ⟨g₁, hg₁0, hg₁f₁, hrg₁⟩ := hr₁
    obtain ⟨g₂, hg₂0, hg₂f₂, hrg₂⟩ := hr₂
    exact ⟨g₁ + g₂,
      fun x => add_nonneg (hg₁0 x) (hg₂0 x),
      fun x => show g₁ x + g₂ x ≤ f₁ x + f₂ x from add_le_add (hg₁f₁ x) (hg₂f₂ x),
      by rw [← hrr, hrg₁, hrg₂, map_add]⟩

/-- Homogeneity of `posPartSup` under multiplication by a positive scalar. -/
lemma posPartSup_smul_pos (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) (hf : ∀ x, 0 ≤ f x)
    (c : ℝ) (hc : 0 < c) :
    posPartSup u (c • f) = c * posPartSup u f := by
  unfold posPartSup
  have h_eq : posPartSet u (c • f) = (fun r => c * r) '' posPartSet u f := by
    ext r; constructor
    · rintro ⟨g, hg0, hgcf, rfl⟩
      refine ⟨u (c⁻¹ • g), ⟨c⁻¹ • g, fun x => ?_, fun x => ?_, rfl⟩, ?_⟩
      · show c⁻¹ * g x ≥ 0; exact mul_nonneg (inv_nonneg.mpr hc.le) (hg0 x)
      · show c⁻¹ * g x ≤ f x; rw [inv_mul_le_iff₀ hc]; exact hgcf x
      · show (fun r => c * r) (u (c⁻¹ • g)) = u g
        simp only; rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    · rintro ⟨_, ⟨h, hh0, hhf, rfl⟩, rfl⟩
      refine ⟨c • h, fun x => ?_, fun x => ?_, ?_⟩
      · show c * h x ≥ 0; exact mul_nonneg hc.le (hh0 x)
      · show c * h x ≤ c * f x; exact mul_le_mul_of_nonneg_left (hhf x) hc.le
      · rw [map_smul, smul_eq_mul]
  rw [h_eq]
  symm; exact Monotone.map_csSup_of_continuousAt
    (continuous_const.mul continuous_id |>.continuousAt)
    (fun _ _ h => mul_le_mul_of_nonneg_left h hc.le)
    (posPartSet_nonempty u f hf)
    (posPartSet_bddAbove u f hf)

/-- Homogeneity of `posPartSup` under multiplication by a nonnegative scalar. -/
lemma posPartSup_smul_nonneg (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X)
    (hf : ∀ x, 0 ≤ f x) (c : ℝ) (hc : 0 ≤ c) :
    posPartSup u (c • f) = c * posPartSup u f := by
  rcases eq_or_lt_of_le hc with rfl | hc_pos
  · simp only [zero_smul, zero_mul, posPartSup_zero]
  · exact posPartSup_smul_pos u f hf c hc_pos

/-- Well-definedness of the positive part on signed decompositions: if `f = h₁ - h₂` with
`h₁, h₂ ≥ 0`, then `posPartSup u f⁺ - posPartSup u f⁻ = posPartSup u h₁ - posPartSup u h₂`. -/
lemma posPartSup_well_defined (u : C₀Map X →L[ℝ] ℝ) (f h₁ h₂ : C₀Map X)
    (hh₁ : ∀ x, 0 ≤ h₁ x) (hh₂ : ∀ x, 0 ≤ h₂ x) (hf : f = h₁ - h₂) :
    posPartSup u (zeroAtInftyPosPart f) - posPartSup u (zeroAtInftyNegPart f) =
    posPartSup u h₁ - posPartSup u h₂ := by

  have hkey : ∀ x, zeroAtInftyPosPart f x + h₂ x = h₁ x + zeroAtInftyNegPart f x := by
    intro x
    simp only [posPart_apply, negPart_apply]
    have hfx : f x = h₁ x - h₂ x := by
      have := DFunLike.congr_fun hf x
      simp only [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply] at this; exact this
    rw [hfx]
    rcases le_or_gt (h₁ x - h₂ x) 0 with hle | hgt
    · rw [max_eq_right hle, zero_add, max_eq_left (by linarith)]; ring
    · rw [max_eq_left hgt.le, max_eq_right (by linarith), add_zero]; ring

  have heq_fn : zeroAtInftyPosPart f + h₂ = h₁ + zeroAtInftyNegPart f := by
    ext x; exact hkey x

  have h1 := posPartSup_add u (zeroAtInftyPosPart f) h₂ (posPart_nonneg f) hh₂
  have h2 := posPartSup_add u h₁ (zeroAtInftyNegPart f) hh₁ (negPart_nonneg f)
  rw [heq_fn] at h1
  linarith

end PosPartConstruction
end ContinuousFunctions
