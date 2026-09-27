import sympy.stats.policy_trajectory.markov
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The discounted conditional reward series of the trajectory model is summable for `γ ∈ [0, 1)`:
`Summable (k ↦ γ ^ k * 𝔼[r[t + k] | B])`, so the sympy `γ ** Stack[k](k) @ 𝔼[r[t:] | B]` is a genuine sum.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (B : Set (ℕ → Step S A))
  (t : ℕ) :
-- imply
  Summable (fun k => γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|B]) := by
-- proof
  classical
  exact summable_cond M θ h₀ B t


-- created on 2026-09-26
