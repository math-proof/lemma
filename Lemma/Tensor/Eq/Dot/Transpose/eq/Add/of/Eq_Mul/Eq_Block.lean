import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import sympy.Basic
open Matrix


@[main]
private lemma position_representation.rotary
  {h : ℕ}
  {b t : ℝ}
  {θ : Fin h → ℝ}
  {R : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) ℝ}
-- given
  (_h₀ : ∀ k : Fin h, θ k = t / b ^ (2 * (k : ℝ) / (2 * h)))
  (h₁ : R = Matrix.fromBlocks (Matrix.diagonal fun k => Real.cos (θ k)) (-Matrix.diagonal fun k => Real.sin (θ k))
    (Matrix.diagonal fun k => Real.sin (θ k)) (Matrix.diagonal fun k => Real.cos (θ k)))
  (x : Fin h ⊕ Fin h → ℝ) :
-- imply
  Rᵀ *ᵥ x = fun a => x a * Real.cos (Sum.elim θ θ a) +
    Sum.elim (fun k => x (Sum.inr k)) (fun k => -x (Sum.inl k)) a * Real.sin (Sum.elim θ θ a) := by
-- proof
  subst h₁
  funext a
  rcases a with k | k <;>
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_mulVec, Matrix.mulVec_diagonal] <;>
    ring


-- created on 2026-09-27
