import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Integral.eq.Sum_Sum_SMul
import Lemma.Random.AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.Integrable_G.of.In_Ico
import Lemma.Random.Integral_MulEqSAndEqAG.eq.MulMulRealPreimageSProbQ.of.In_Ico
import Lemma.Real.SMul.eq.Sum_Sum_SMul
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
import Lemma.Real.StronglyMeasurable.discrete
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[G[t] • ψ(s[t], a[t])] = 𝔼[Q(s[t], a[t]) • ψ(s[t], a[t])]`
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
  (t : ℕ)
  (ψ : S → A → E) :
-- imply
  ∫ ω, G γ t ω • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, M.Q θ γ t (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ) := by
-- proof
  have hX : Measurable (fun ω : ℕ → ℝ × S × A => (s t ω, a t ω)) := (Random.Measurable_S t).prodMk (Random.Measurable_A t)
  have hI : ∀ x u, Integrable (fun ω => (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * G γ t ω)
      (M θ) := by
    intro x u
    refine Integrable.of_bound (C := (1 - γ)⁻¹ * |M.env.R|) ?_ ?_
    · exact (((StronglyMeasurable.discrete (fun p : S × A => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0)).comp_measurable
        hX).aestronglyMeasurable).mul (Integrable_G.of.In_Ico (M := M) θ h₀ t).1
    · filter_upwards [AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico (M := M) θ h₀ t] with ω h
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by split_ifs <;> simp) |>.trans h.2
  rw [Integral.eq.Sum_Sum_SMul (M := M) θ t (fun y u => M.Q θ γ t y u • ψ y u)]
  simp_rw [SMul.eq.Sum_Sum_SMul t _ (G γ t _) ψ]
  rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun u _ => (hI x u).smul_const _]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_finsetSum _ fun u _ => (hI x u).smul_const _]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [integral_smul_const, Integral_MulEqSAndEqAG.eq.MulMulRealPreimageSProbQ.of.In_Ico (M := M) θ h₀ t, smul_smul]


-- created on 2026-10-06
