import sympy.stats.policy_trajectory.advantage
import sympy.Basic
import Lemma.Real.SMul.eq.Sum_Sum_SMul
import Lemma.Random.Integrable_SMulSubAddRMul_VcVc.of.In_Ico
import Lemma.Random.Integral_MulEqSAndEqAGetSubAddRMul_VcVc.eq.Zero.of.Le.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
For `t ≤ n`, the residual `δ[n+1] = r[n+1] + γ * Vc(s[n+2]) - Vc(s[n+1])` is orthogonal to every function of `(s[t], a[t])`:
`𝔼[δ[n+1] • ψ(s[t], a[t])] = 0`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {γ : ℝ}
  {E : Type*}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [CompleteSpace E]
-- given
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (t n : ℕ)
  (h₁ : t ≤ n)
  (ψ : S → A → E) :
-- imply
  ∫ ω, (reward (n + 1) ω + γ * M.Vc θ γ (state (n + 1 + 1) ω) - M.Vc θ γ (state (n + 1) ω)) •
    ψ (state t ω) (action t ω) ∂(M θ) = 0 := by
-- proof
  have hI : ∀ x u, Integrable (fun ω => (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) *
      (reward (n + 1) ω + γ * M.Vc θ γ (state (n + 1 + 1) ω) - M.Vc θ γ (state (n + 1) ω))) (M θ) := by
    intro x u
    refine (Random.Integrable_SMulSubAddRMul_VcVc.of.In_Ico (M := M) θ h₀ t (n + 1)
      (fun x' u' => if x' = x ∧ u' = u then (1:ℝ) else 0)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [smul_eq_mul]
    ring
  have e : (fun ω => (reward (n + 1) ω + γ * M.Vc θ γ (state (n + 1 + 1) ω) - M.Vc θ γ (state (n + 1) ω)) •
      ψ (state t ω) (action t ω)) = fun ω => ∑ x, ∑ u, ((if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) *
        (reward (n + 1) ω + γ * M.Vc θ γ (state (n + 1 + 1) ω) - M.Vc θ γ (state (n + 1) ω))) • ψ x u :=
    funext fun ω => Real.SMul.eq.Sum_Sum_SMul t ω _ ψ
  rw [e, integral_finsetSum _ fun x _ => integrable_finsetSum _ fun u _ => (hI x u).smul_const _]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [integral_finsetSum _ fun u _ => (hI x u).smul_const _]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [integral_smul_const, Random.Integral_MulEqSAndEqAGetSubAddRMul_VcVc.eq.Zero.of.Le.In_Ico (M := M) θ h₀ t n h₁ x u, zero_smul]


-- created on 2026-10-06
