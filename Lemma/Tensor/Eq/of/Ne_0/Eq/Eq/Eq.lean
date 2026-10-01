import sympy.stats.hidden_markov_sequence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import sympy.Basic


@[main]
private lemma crf.markov
  {Y : Type*}
  {P : ℕ → (ℕ → Y) → ℝ}
  {π : Y → ℝ}
  {T : Y → Y → ℝ}
  {E : ℕ → Y → ℝ}
-- given
  (h : IsHiddenMarkovSeq P π T E) :
-- imply
  ∀ (ys : ℕ → Y) (t : ℕ), P t ys = E 0 (ys 0) * π (ys 0) * ∏ i ∈ Finset.Ico 1 (t + 1), T (ys (i - 1)) (ys i) * E i (ys i) := by
-- proof
  intro ys t
  induction t with
  | zero =>
    simp [(h ys).1]
  | succ t ih =>
    rw [(h ys).2 t, ih, Finset.prod_Ico_succ_top (by omega : 1 ≤ t + 1), Nat.add_sub_cancel]
    ring


@[main]
private lemma policy_gradient_theorem
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {T : ℕ}
  {C : ℝ}
  {p : E → ℕ → ℝ}
-- given
  (h₀ : 0 < C)
  (h₁ : ∀ θ t, 0 < p θ t)
  (h₂ : ∀ θ t, DifferentiableAt ℝ (fun θ => p θ t) θ) :
-- imply
  ∀ θ₀ : E, fderiv ℝ (fun θ => Real.log (C * ∏ t ∈ Finset.range T, p θ t)) θ₀ = ∑ t ∈ Finset.range T, fderiv ℝ (fun θ => Real.log (p θ t)) θ₀ := by
-- proof
  intro θ₀
  have e : (fun θ => Real.log (C * ∏ t ∈ Finset.range T, p θ t)) = fun θ => Real.log C + ∑ t ∈ Finset.range T, Real.log (p θ t) := by
    funext θ
    rw [Real.log_mul h₀.ne' (Finset.prod_pos fun t _ => h₁ θ t).ne', Real.log_prod (fun t _ => (h₁ θ t).ne')]
  rw [e, fderiv_const_add, fderiv_fun_sum (fun t _ => (h₂ θ₀ t).log (h₁ θ₀ t).ne')]


-- created on 2026-09-27
