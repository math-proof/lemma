import Lemma.Real.Grad.Sum_Exp.eq.Sum_Mul_Exp.of.All_DifferentiableAt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import sympy.Basic


/--
Gradient of softmax, component-wise (py: `Derivative[x](softmax(f(x)))` for a vector `x`).
Here `F i t` stands for the `i`-th logit `f(x)ᵢ` as a function of one coordinate `t = xₖ`
(the others fixed), so `deriv (F i) t = ∂ₖ fᵢ(x)`.  With \(s_i=\mathrm{softmax}(F)_i\):
\[
\frac{\partial}{\partial x_k}s_j=s_j\Big(\partial_k f_j-\sum_i s_i\,\partial_k f_i\Big).
\]
-/
@[main]
private lemma vector.using.Stack
  {n : ℕ}
  {F : Fin n → ℝ → ℝ}
  {t : ℝ}
-- given
  (h : ∀ i, DifferentiableAt ℝ (F i) t)
  (j : Fin n) :
-- imply
  deriv (fun t => Real.exp (F j t) / ∑ i, Real.exp (F i t)) t =
    Real.exp (F j t) / (∑ i, Real.exp (F i t)) *
      (deriv (F j) t - ∑ i, Real.exp (F i t) / (∑ i, Real.exp (F i t)) * deriv (F i) t) := by
-- proof
  have hS : 0 < ∑ i, Real.exp (F i t) := by
    apply Finset.sum_pos (fun i _ => Real.exp_pos _)
    exact ⟨j, Finset.mem_univ j⟩
  have hnum := (h j).hasDerivAt.exp
  have hden := Real.Grad.Sum_Exp.eq.Sum_Mul_Exp.of.All_DifferentiableAt h
  have hq := HasDerivAt.fun_div hnum hden hS.ne'
  rw [hq.deriv]
  set S := ∑ i, Real.exp (F i t) with hSdef
  have h1 : ∑ i, Real.exp (F i t) / S * deriv (F i) t = (∑ i, Real.exp (F i t) * deriv (F i) t) / S := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  field_simp

/--
Same statement as `vector.using.Stack` (py `Real.Grad.Softmax.eq.Mul.Softmax.vector` proves the same
equation by a different route, via the vector-valued gradient; here both are the component-wise form).
-/
@[main]
private lemma vector
  {n : ℕ}
  {F : Fin n → ℝ → ℝ}
  {t : ℝ}
-- given
  (h : ∀ i, DifferentiableAt ℝ (F i) t)
  (j : Fin n) :
-- imply
  deriv (fun t => Real.exp (F j t) / ∑ i, Real.exp (F i t)) t =
    Real.exp (F j t) / (∑ i, Real.exp (F i t)) *
      (deriv (F j) t - ∑ i, Real.exp (F i t) / (∑ i, Real.exp (F i t)) * deriv (F i) t) :=
-- proof
  vector.using.Stack h j


-- created on 2026-10-01