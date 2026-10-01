import sympy.Basic
import sympy.functions.elementary.masked_softmax
import Mathlib.Analysis.SpecialFunctions.Exp
open Matrix


@[main]
private lemma scaled_dot_product_attention
  {n d : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
  {V : Matrix (Fin n) (Fin d) ℝ} :
-- imply
  (Matrix.of fun i j => Real.exp (A i j) / ∑ k, Real.exp (A i k)) * V =
    Matrix.of fun i => Matrix.vecMul (fun j => Real.exp (A i j) / ∑ k, Real.exp (A i k)) V := by
-- proof
  ext i l
  rfl


@[main]
private lemma gpt.batched
  {m n d : ℕ}
  {A : Fin m → Fin n → Fin n → ℝ}
  {V : Fin m → Fin n → Fin d → ℝ} :
-- imply
  (fun b i l => ∑ j, maskedSoftmax (A b i) (fun j => if j ≤ i then 1 else 0) j * V b j l) =
    fun b i l => ∑ j ∈ Finset.univ.filter (· ≤ i), Real.exp (A b i j) / (∑ k ∈ Finset.univ.filter (· ≤ i), Real.exp (A b i k)) * V b j l := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  funext b i l
  simp only [maskedSoftmax, key, ite_div, zero_div, ite_mul, zero_mul, Finset.sum_filter]


-- created on 2021-08-07
-- updated on 2026-09-27
