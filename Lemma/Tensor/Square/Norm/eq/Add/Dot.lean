import sympy.functions.elementary.complexes
import sympy.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
open Complex


@[main]
private lemma main
  {n : ℕ}
  {x y : Fin n → ℂ} :
-- imply
  √(∑ i, ‖x i + y i‖ ^ 2) ^ 2 = √(∑ i, ‖x i‖ ^ 2) ^ 2 + √(∑ i, ‖y i‖ ^ 2) ^ 2 + 2 * (x ⬝ᵥ (fun i => ~(y i))).re := by
-- proof
  have e : ∀ f : Fin n → ℂ, √(∑ i, ‖f i‖ ^ 2) ^ 2 = ∑ i, ‖f i‖ ^ 2 :=
    fun _ => Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  simp only [e, dotProduct, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im]
  ring


-- created on 2023-06-24
