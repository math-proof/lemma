import sympy.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Matrix


@[main]
private lemma position_representation.plane
  {mr mc : ℕ}
  {br bc lr lc : ℝ}
  {θr : ℤ → Fin mr → ℝ}
  {θc : ℤ → Fin mc → ℝ}
  {R : ℤ → ℤ → Matrix (Fin (mr + mc) ⊕ Fin (mr + mc)) (Fin (mr + mc) ⊕ Fin (mr + mc)) ℝ}
  {r c : ℕ → ℤ}
  {t : ℕ}
  {x : Fin (mr + mc) ⊕ Fin (mr + mc) → ℝ}
-- given
  (_h₀ : ∀ i h, θr i h = lr * i / br ^ ((h : ℝ) / mr))
  (_h₁ : ∀ j h, θc j h = lc * j / bc ^ ((h : ℝ) / mc))
  (h₂ : ∀ i j, R i j = Matrix.fromBlocks (Matrix.diagonal fun k => Real.cos (Fin.append (θr i) (θc j) k)) (-Matrix.diagonal fun k => Real.sin (Fin.append (θr i) (θc j) k)) (Matrix.diagonal fun k => Real.sin (Fin.append (θr i) (θc j) k)) (Matrix.diagonal fun k => Real.cos (Fin.append (θr i) (θc j) k))) :
-- imply
  R (r t) (c t) *ᵥ x = fun s => Sum.elim (fun a => x (Sum.inl a) * Real.cos (Fin.append (θr (r t)) (θc (c t)) a) + -x (Sum.inr a) * Real.sin (Fin.append (θr (r t)) (θc (c t)) a))
    (fun a => x (Sum.inr a) * Real.cos (Fin.append (θr (r t)) (θc (c t)) a) + x (Sum.inl a) * Real.sin (Fin.append (θr (r t)) (θc (c t)) a)) s := by
-- proof
  rw [h₂, Matrix.fromBlocks_mulVec]
  funext s
  cases s <;> simp [Matrix.mulVec_diagonal] <;> ring


-- created on 2026-09-27
