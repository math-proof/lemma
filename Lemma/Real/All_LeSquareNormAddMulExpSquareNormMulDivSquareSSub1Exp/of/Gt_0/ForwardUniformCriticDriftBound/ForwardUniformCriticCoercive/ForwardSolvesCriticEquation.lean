import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus
import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {m : ℕ}
  {lambdaC : ℝ}
  {Bb : ℝ}
  {A : ℝ → Matrix (Fin m) (Fin m) ℝ}
  {b : ℝ → EuclideanVec m}
  {w : ℝ → EuclideanVec m}
-- given
  (h₀ : ForwardSolvesCriticEquation A b w)
  (h₁ : ForwardUniformCriticCoercive lambdaC A)
  (h₂ : ForwardUniformCriticDriftBound Bb b)
  (h₃ : 0 < lambdaC) :
-- imply
  ∀ t, 0 ≤ t → ‖w t‖ ^ 2 ≤ Real.exp (-lambdaC * t) * ‖w 0‖ ^ 2 + Bb ^ 2 / lambdaC ^ 2 * (1 - Real.exp (-lambdaC * t)) := by
-- proof
  intro T hT
  have hd : ∀ t, 0 ≤ t → HasDerivWithinAt (fun s => ‖w s‖ ^ 2) (2 * inner ℝ (w t) (critic_velocity A b w t)) (Set.Ici t) t :=
    fun t ht => (h₀.hasDeriv t ht).norm_sq
  have hbound : ∀ t, 0 ≤ t → 2 * inner ℝ (w t) (critic_velocity A b w t) ≤ -lambdaC * ‖w t‖ ^ 2 + Bb ^ 2 / lambdaC := by
    intro t ht
    have hc := h₁ t ht (w t)
    have hi : inner ℝ (w t) (b t) ≤ ‖w t‖ * Bb := (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (h₂ t ht) (norm_nonneg _))
    have hsplit : inner ℝ (w t) (critic_velocity A b w t) = inner ℝ (w t) (b t) - critic_quadratic_form (A t) (w t) := inner_sub_right _ _ _
    have hsq := div_nonneg (sq_nonneg (lambdaC * ‖w t‖ - Bb)) h₃.le
    have e : (lambdaC * ‖w t‖ - Bb) ^ 2 / lambdaC = lambdaC * ‖w t‖ ^ 2 - 2 * (‖w t‖ * Bb) + Bb ^ 2 / lambdaC := by
      field_simp
      ring
    rw [hsplit]
    linarith
  have hg := le_gronwallBound_of_liminf_deriv_right_le (f := fun s => ‖w s‖ ^ 2) (f' := fun t => 2 * inner ℝ (w t) (critic_velocity A b w t))
    (δ := ‖w 0‖ ^ 2) (K := -lambdaC) (ε := Bb ^ 2 / lambdaC) (a := 0) (b := T) (h₀.cont.norm.pow 2).continuousOn
    (fun x hx r hr => (hd x hx.1).liminf_right_slope_le hr) le_rfl (fun x hx => hbound x hx.1) T ⟨hT, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 (neg_ne_zero.2 h₃.ne')] at hg
  simp only [sub_zero] at hg
  refine hg.trans_eq ?_
  field_simp
  ring


-- created on 2026-09-26
