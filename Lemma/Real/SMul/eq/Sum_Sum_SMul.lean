import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
Indicator expansion over the finite state / action spaces:
`c • ψ(s[t], a[t]) = ∑ x, ∑ u, (1{s[t] = x ∧ a[t] = u} * c) • ψ x u`.
-/
@[main]
private lemma main
  [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  {E : Type*}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
-- given
  (t : ℕ)
  (ω : ℕ → ℝ × S × A)
  (c : ℝ)
  (ψ : S → A → E) :
-- imply
  c • ψ (state t ω) (action t ω) =
    ∑ x, ∑ u, ((if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * c) • ψ x u := by
-- proof
  rw [Finset.sum_eq_single (state t ω) (fun b _ hb => Finset.sum_eq_zero fun u _ => by simp [Ne.symm hb])
    (by simp)]
  rw [Finset.sum_eq_single (action t ω) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp


-- created on 2026-10-06
