import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Summable_MulPowIntegral_R_Add.of.In_Ico
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


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
  (B : Set (ℕ → ℝ × S × A))
  (t : ℕ) :
-- imply
  Summable (fun k => γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|B]) := by
-- proof
  classical
  exact Summable_MulPowIntegral_R_Add.of.In_Ico (M := M) h₀ θ B t


-- created on 2026-09-26
