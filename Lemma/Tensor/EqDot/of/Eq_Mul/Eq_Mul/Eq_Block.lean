import sympy.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Matrix


@[path]
private lemma position_representation.plane
  {mr mc : ℕ}
  {br bc lr lc : ℝ}
  {θr : ℤ → Fin mr → ℝ}
  {θc : ℤ → Fin mc → ℝ}
  {R : ℤ → ℤ → Matrix (Fin (mr + mc) ⊕ Fin (mr + mc)) (Fin (mr + mc) ⊕ Fin (mr + mc)) ℝ}
  {i j i' j' : ℤ}
-- given
  (h₀ : ∀ i h, θr i h = lr * i / br ^ ((h : ℝ) / mr))
  (h₁ : ∀ j h, θc j h = lc * j / bc ^ ((h : ℝ) / mc))
  (h₂ : ∀ i j, R i j = Matrix.fromBlocks (Matrix.diagonal fun k => Real.cos (Fin.append (θr i) (θc j) k)) (-Matrix.diagonal fun k => Real.sin (Fin.append (θr i) (θc j) k)) (Matrix.diagonal fun k => Real.sin (Fin.append (θr i) (θc j) k)) (Matrix.diagonal fun k => Real.cos (Fin.append (θr i) (θc j) k))) :
-- imply
  (R i' j')ᵀ * R i j = R (i - i') (j - j') := by
-- proof
  have hs : ∀ k, Fin.append (θr (i - i')) (θc (j - j')) k = Fin.append (θr i) (θc j) k - Fin.append (θr i') (θc j') k := by
    intro k
    refine Fin.addCases (fun a => ?_) (fun a => ?_) k
    ·
      simp only [Fin.append_left, h₀]
      push_cast
      ring
    ·
      simp only [Fin.append_right, h₁]
      push_cast
      ring
  rw [h₂, h₂, h₂, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  congr 1 <;> ext a c <;> by_cases hac : a = c <;> simp [hac, hs, Real.cos_sub, Real.sin_sub] <;> ring


-- created on 2026-09-27
