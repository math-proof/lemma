import Lemma.Real.Grad.Sum_Exp.eq.Sum_Mul_Exp.of.All_DifferentiableAt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
open Real


/--
Component-wise gradient of softmax: with `sⱼ = exp(Fⱼ) / ∑ exp(Fᵢ)`,
`∂ₛⱼ = sⱼ (∂Fⱼ - ∑ sᵢ ∂Fᵢ)`.
-/
@[path]
private lemma main
  {n : ℕ}
  {F : Fin n → ℝ → ℝ}
  {t : ℝ}
-- given
  (h₀ : ∀ i, DifferentiableAt ℝ (F i) t)
  (j : Fin n) :
-- imply
  deriv (fun t => Real.exp (F j t) / ∑ i, Real.exp (F i t)) t =
    Real.exp (F j t) / (∑ i, Real.exp (F i t)) *
      (deriv (F j) t - ∑ i, Real.exp (F i t) / (∑ i, Real.exp (F i t)) * deriv (F i) t) := by
-- proof
  have hS : 0 < ∑ i, Real.exp (F i t) := by
    apply Finset.sum_pos (fun i _ => Real.exp_pos _)
    exact ⟨j, Finset.mem_univ j⟩
  have hnum := (h₀ j).hasDerivAt.exp
  have hden := Grad.Sum_Exp.eq.Sum_Mul_Exp.of.All_DifferentiableAt h₀
  have hq := HasDerivAt.fun_div hnum hden hS.ne'
  rw [hq.deriv]
  set S := ∑ i, Real.exp (F i t) with hSdef
  have h1 : ∑ i, Real.exp (F i t) / S * deriv (F i) t =
      (∑ i, Real.exp (F i t) * deriv (F i) t) / S := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  field_simp


-- created on 2023-03-18
-- updated on 2026-10-17
