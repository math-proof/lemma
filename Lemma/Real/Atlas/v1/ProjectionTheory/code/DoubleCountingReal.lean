import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProjectionTheory.code.DoubleCountingReal.Part3
open Finset BigOperators ProjectionTheory


namespace ProjectionTheory

/--
[double_counting_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingReal.lean)
-/
@[path]
lemma double_counting_real
  {setup : DoubleCountingRealSetup}
  {collisionCount : ℝ}
-- given
  (hX_pos : 0 < setup.cardX)
  (hLower : ∃ c₁ : ℝ, c₁ > 0 ∧ c₁ * (setup.cardD : ℝ) * ((setup.cardX : ℝ) ^ 2 / (setup.S : ℝ)) ≤ collisionCount)
  (hUpper : ∃ c₂ : ℝ, c₂ > 0 ∧ collisionCount ≤ c₂ * (setup.cardX : ℝ) * ((∑ k ∈ dyadicExponentRange setup.R, setup.N_X (2 ^ k) * setup.N_D ((2 : ℝ) ^ k)⁻¹ : ℕ) : ℝ)) :
-- imply
  ∃ C : ℝ, C > 0 ∧ (setup.cardD : ℝ) ≤ C * ((setup.S : ℝ) / (setup.cardX : ℝ)) * (dyadicSum setup : ℝ) := by
-- proof
  obtain ⟨c₁, hc₁_pos, hLower⟩ := hLower
  obtain ⟨c₂, hc₂_pos, hUpper⟩ := hUpper
  have hchain : c₁ * (setup.cardD : ℝ) * ((setup.cardX : ℝ) ^ 2 / (setup.S : ℝ)) ≤
    c₂ * (setup.cardX : ℝ) * (dyadicSum setup : ℝ) :=
    le_trans hLower hUpper
  refine ⟨c₂ / c₁, div_pos hc₂_pos hc₁_pos, ?_⟩
  have hX_pos' : (0 : ℝ) < (setup.cardX : ℝ) := Nat.cast_pos.mpr hX_pos
  have hS_pos' : (0 : ℝ) < (setup.S : ℝ) := Nat.cast_pos.mpr setup.hS_pos
  have hc₁X_pos : (0 : ℝ) < c₁ * (setup.cardX : ℝ) := mul_pos hc₁_pos hX_pos'
  have hkey : (setup.cardD : ℝ) * (c₁ * (setup.cardX : ℝ)) ≤
    c₂ * (setup.S : ℝ) * (dyadicSum setup : ℝ) := by
    have h1 : c₁ * (setup.cardD : ℝ) * ((setup.cardX : ℝ) ^ 2 / (setup.S : ℝ)) =
      (setup.cardD : ℝ) * (c₁ * (setup.cardX : ℝ)) * ((setup.cardX : ℝ) / (setup.S : ℝ)) := by
      ring
    have h2 : c₂ * (setup.cardX : ℝ) * (dyadicSum setup : ℝ) =
      c₂ * (setup.S : ℝ) * (dyadicSum setup : ℝ) * ((setup.cardX : ℝ) / (setup.S : ℝ)) := by
      field_simp
    nlinarith [div_pos hX_pos' hS_pos']
  rw [show c₂ / c₁ * ((setup.S : ℝ) / (setup.cardX : ℝ)) * (dyadicSum setup : ℝ) =
    c₂ * (setup.S : ℝ) * (dyadicSum setup : ℝ) / (c₁ * (setup.cardX : ℝ)) from by ring]
  exact (le_div_iff₀ hc₁X_pos).mpr hkey

end ProjectionTheory


-- created on 2026-10-23
