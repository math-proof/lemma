import Lemma.Real.Grad.Sum_Exp.eq.Sum_Mul_Exp.of.All_DifferentiableAt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Matrix.Mul
import sympy.Basic


/--
Softmax policy (py: `Pr(a | s) = softmax(φ(s) @ θ)[a]`) has the score function
\(\nabla_\theta\log\pi(a\mid s)=\phi_a-\mathbb E_{b\sim\pi}[\phi_b]\).
Here `Φ = φ(s)` is the `m × n` feature matrix and the identity is stated per component `k`
of `θ` (ordinary derivative in the coordinate `θₖ`, the others fixed):
\[
\frac{\partial}{\partial\theta_k}\log\mathrm{softmax}(\Phi\theta)_a
=\Phi_{ak}-\sum_b\mathrm{softmax}(\Phi\theta)_b\,\Phi_{bk}.
\]
-/
@[main]
private lemma softmax_policy
  {m n : ℕ}
  {Φ : Matrix (Fin m) (Fin n) ℝ}
  {θ : Fin n → ℝ}
-- given
  (a : Fin m)
  (k : Fin n) :
-- imply
  deriv (fun t => Real.log (Real.exp ((Φ.mulVec (Function.update θ k t)) a) / ∑ b, Real.exp ((Φ.mulVec (Function.update θ k t)) b))) (θ k) =
    Φ a k - ∑ b, Real.exp ((Φ.mulVec θ) b) / (∑ c, Real.exp ((Φ.mulVec θ) c)) * Φ b k := by
-- proof
  have hL : ∀ b, HasDerivAt (fun t => (Φ.mulVec (Function.update θ k t)) b) (Φ b k) (θ k) := by
    intro b
    simp only [Matrix.mulVec, dotProduct]
    have : HasDerivAt (fun t => ∑ k', Φ b k' * Function.update θ k t k') (∑ k', if k' = k then Φ b k else 0) (θ k) := by
      apply HasDerivAt.fun_sum
      intro k' _
      by_cases hk : k' = k
      · subst hk
        simpa using (hasDerivAt_id (θ k')).const_mul (Φ b k')
      · simp only [hk, if_false, Function.update_of_ne hk]
        exact hasDerivAt_const _ _
    simpa using this
  have hup : Function.update θ k (θ k) = θ := Function.update_eq_self k θ
  have hd : ∀ b, DifferentiableAt ℝ (fun t => (Φ.mulVec (Function.update θ k t)) b) (θ k) :=
    fun b => (hL b).differentiableAt
  have hden : 0 < ∑ b, Real.exp ((Φ.mulVec θ) b) :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) ⟨a, Finset.mem_univ a⟩
  have hnum := ((hd a).hasDerivAt).exp
  have hs := Real.Grad.Sum_Exp.eq.Sum_Mul_Exp.of.All_DifferentiableAt hd
  have hden' : (∑ b, Real.exp ((Φ.mulVec (Function.update θ k (θ k))) b)) ≠ 0 := by
    rw [hup]; exact hden.ne'
  have hq := HasDerivAt.fun_div hnum hs hden'
  have hlog := hq.log (by rw [hup]; exact (div_pos (Real.exp_pos _) hden).ne')
  rw [hlog.deriv]
  simp only [fun b => (hL b).deriv, hup]
  set S := ∑ i, Real.exp ((Φ.mulVec θ) i) with hS
  have hSne : S ≠ 0 := hden.ne'
  have h1 : ∑ b, Real.exp ((Φ.mulVec θ) b) / S * Φ b k = (∑ b, Real.exp ((Φ.mulVec θ) b) * Φ b k) / S := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  have hea := (Real.exp_pos ((Φ.mulVec θ) a)).ne'
  field_simp


-- created on 2023-03-18
-- updated on 2023-03-24
