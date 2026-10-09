import sympy.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Matrix


@[path]
private lemma position_representation.space
  {mr mc mz : ℕ}
  {br bc bz lr lc lz : ℝ}
  {θr : ℤ → Fin mr → ℝ}
  {θc : ℤ → Fin mc → ℝ}
  {θz : ℤ → Fin mz → ℝ}
  {R : ℤ → ℤ → ℤ → Matrix (Fin (mr + mc + mz) ⊕ Fin (mr + mc + mz)) (Fin (mr + mc + mz) ⊕ Fin (mr + mc + mz)) ℝ}
  {r c z : ℕ → ℤ}
  {t : ℕ}
  {x : Fin (mr + mc + mz) ⊕ Fin (mr + mc + mz) → ℝ}
-- given
  (_h₀ : ∀ i h, θr i h = lr * i / br ^ ((h : ℝ) / mr))
  (_h₁ : ∀ j h, θc j h = lc * j / bc ^ ((h : ℝ) / mc))
  (_h₂ : ∀ k h, θz k h = lz * k / bz ^ ((h : ℝ) / mz))
  (h₃ : ∀ i j k, R i j k = Matrix.fromBlocks (Matrix.diagonal fun q => Real.cos (Fin.append (Fin.append (θr i) (θc j)) (θz k) q)) (-Matrix.diagonal fun q => Real.sin (Fin.append (Fin.append (θr i) (θc j)) (θz k) q)) (Matrix.diagonal fun q => Real.sin (Fin.append (Fin.append (θr i) (θc j)) (θz k) q)) (Matrix.diagonal fun q => Real.cos (Fin.append (Fin.append (θr i) (θc j)) (θz k) q))) :
-- imply
  R (r t) (c t) (z t) *ᵥ x = fun s => Sum.elim (fun a => x (Sum.inl a) * Real.cos (Fin.append (Fin.append (θr (r t)) (θc (c t))) (θz (z t)) a) + -x (Sum.inr a) * Real.sin (Fin.append (Fin.append (θr (r t)) (θc (c t))) (θz (z t)) a))
    (fun a => x (Sum.inr a) * Real.cos (Fin.append (Fin.append (θr (r t)) (θc (c t))) (θz (z t)) a) + x (Sum.inl a) * Real.sin (Fin.append (Fin.append (θr (r t)) (θc (c t))) (θz (z t)) a)) s := by
-- proof
  rw [h₃, Matrix.fromBlocks_mulVec]
  funext s
  cases s <;> simp [Matrix.mulVec_diagonal] <;> ring


-- created on 2026-09-27
