import sympy.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Matrix


@[main]
private lemma main
  {m : ℕ}
  {b l : ℝ}
  {θ : ℤ → Fin m → ℝ}
  {i t : ℤ}
-- given
  (h : ∀ i j, θ i j = l * i / b ^ ((j : ℝ) / m)) :
-- imply
  (Matrix.fromBlocks (Matrix.diagonal fun j => Real.cos (θ t j)) (-Matrix.diagonal fun j => Real.sin (θ t j))
      (Matrix.diagonal fun j => Real.sin (θ t j)) (Matrix.diagonal fun j => Real.cos (θ t j)))ᵀ *
    Matrix.fromBlocks (Matrix.diagonal fun j => Real.cos (θ i j)) (-Matrix.diagonal fun j => Real.sin (θ i j))
      (Matrix.diagonal fun j => Real.sin (θ i j)) (Matrix.diagonal fun j => Real.cos (θ i j)) =
    Matrix.fromBlocks (Matrix.diagonal fun j => Real.cos (θ (i - t) j)) (-Matrix.diagonal fun j => Real.sin (θ (i - t) j))
      (Matrix.diagonal fun j => Real.sin (θ (i - t) j)) (Matrix.diagonal fun j => Real.cos (θ (i - t) j)) := by
-- proof
  have hs : ∀ j, θ (i - t) j = θ i j - θ t j := by
    intro j
    rw [h, h, h]
    push_cast
    ring
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  congr 1 <;> ext a c <;> by_cases hac : a = c <;> simp [hac, hs, Real.cos_sub, Real.sin_sub] <;> ring


@[main]
private lemma transpose
  {m : ℕ}
  {b l : ℝ}
  {θ : ℤ → Fin m → ℝ}
  {R : ℤ → Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ}
  {i t : ℤ}
-- given
  (h₀ : ∀ i j, θ i j = l * i / b ^ ((j : ℝ) / m))
  (h₁ : ∀ i, R i = Matrix.fromBlocks (Matrix.diagonal fun j => Real.cos (θ i j)) (-Matrix.diagonal fun j => Real.sin (θ i j))
      (Matrix.diagonal fun j => Real.sin (θ i j)) (Matrix.diagonal fun j => Real.cos (θ i j))) :
-- imply
  (R t)ᵀ * R i = R (i - t) := by
-- proof
  rw [h₁, h₁, h₁]
  exact main h₀


-- created on 2026-09-27
