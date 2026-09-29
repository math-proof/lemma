import sympy.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Matrix


@[main]
private lemma position_representation.space
  {mr mc mz : ℕ}
  {br bc bz lr lc lz : ℝ}
  {θr : ℤ → Fin mr → ℝ}
  {θc : ℤ → Fin mc → ℝ}
  {θz : ℤ → Fin mz → ℝ}
  {R : ℤ → ℤ → ℤ → Matrix (Fin (mr + mc + mz) ⊕ Fin (mr + mc + mz)) (Fin (mr + mc + mz) ⊕ Fin (mr + mc + mz)) ℝ}
  {i j k i' j' k' : ℤ}
-- given
  (h₀ : ∀ i h, θr i h = lr * i / br ^ ((h : ℝ) / mr))
  (h₁ : ∀ j h, θc j h = lc * j / bc ^ ((h : ℝ) / mc))
  (h₂ : ∀ k h, θz k h = lz * k / bz ^ ((h : ℝ) / mz))
  (h₃ : ∀ i j k, R i j k = Matrix.fromBlocks (Matrix.diagonal fun q => Real.cos (Fin.append (Fin.append (θr i) (θc j)) (θz k) q)) (-Matrix.diagonal fun q => Real.sin (Fin.append (Fin.append (θr i) (θc j)) (θz k) q)) (Matrix.diagonal fun q => Real.sin (Fin.append (Fin.append (θr i) (θc j)) (θz k) q)) (Matrix.diagonal fun q => Real.cos (Fin.append (Fin.append (θr i) (θc j)) (θz k) q))) :
-- imply
  (R i' j' k')ᵀ * R i j k = R (i - i') (j - j') (k - k') := by
-- proof
  have hs : ∀ t, Fin.append (Fin.append (θr (i - i')) (θc (j - j'))) (θz (k - k')) t =
      Fin.append (Fin.append (θr i) (θc j)) (θz k) t - Fin.append (Fin.append (θr i') (θc j')) (θz k') t := by
    intro t
    refine Fin.addCases (fun a => ?_) (fun a => ?_) t
    ·
      refine Fin.addCases (fun b => ?_) (fun b => ?_) a
      ·
        simp only [Fin.append_left, h₀]
        push_cast
        ring
      ·
        simp only [Fin.append_left, Fin.append_right, h₁]
        push_cast
        ring
    ·
      simp only [Fin.append_right, h₂]
      push_cast
      ring
  rw [h₃, h₃, h₃, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  congr 1 <;> ext a c <;> by_cases hac : a = c <;> simp [hac, hs, Real.cos_sub, Real.sin_sub] <;> ring


-- created on 2026-09-27
