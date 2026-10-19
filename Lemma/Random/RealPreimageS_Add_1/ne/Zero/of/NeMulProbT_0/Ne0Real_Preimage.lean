import Lemma.Random.Integrable.of.Measurable
import Lemma.Random.Integral_MulEqS.eq.MulRealSum_MulProbSum_MulT
import Lemma.Random.T.ge.Zero
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Reachability: if `Pr(s[t] = x) ≠ 0` and `π_θ(u | x) * T(x, u, y) ≠ 0` then `Pr(s[t+1] = y) ≠ 0`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (u : A)
  (y : S)
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hP : (M θ).real (s t ⁻¹' {x}) ≠ 0)
  (hz : M.policy.prob θ x u * (M.env.trans (x, u)).real {y} ≠ 0) :
-- imply
  (M θ).real (s (t + 1) ⁻¹' {y}) ≠ 0 := by
-- proof
  have hE : ∫ ω, (if s t ω = x then (1:ℝ) else 0) * (if s (t + 1) ω = y then (1:ℝ) else 0) ∂(M θ) =
      (M θ).real (s t ⁻¹' {x}) * ∑ u', M.policy.prob θ x u' * (M.env.trans (x, u')).real {y} := by
    refine (Integral_MulEqS.eq.MulRealSum_MulProbSum_MulT h₀ (M := M) θ t x (fun y' => if y' = y then (1:ℝ) else 0)).trans ?_
    congr 1
    refine Finset.sum_congr rfl (fun u' _ => ?_)
    congr 1
    simp
  have hpos : 0 < (M θ).real (s t ⁻¹' {x}) * ∑ u', M.policy.prob θ x u' * (M.env.trans (x, u')).real {y} := by
    refine mul_pos (lt_of_le_of_ne measureReal_nonneg (Ne.symm hP)) ?_
    refine lt_of_lt_of_le (lt_of_le_of_ne (mul_nonneg (M.policy.nonneg θ x u) (T.ge.Zero (M := M) x u y))
      (Ne.symm hz)) ?_
    apply Finset.single_le_sum (f := fun u' => M.policy.prob θ x u' * (M.env.trans (x, u')).real {y})
      (fun u' _ => mul_nonneg (M.policy.nonneg _ _ _) (T.ge.Zero (M := M) _ _ _)) (Finset.mem_univ u)
  have hle : ∫ ω, (if s t ω = x then (1:ℝ) else 0) * (if s (t + 1) ω = y then (1:ℝ) else 0) ∂(M θ) ≤
      (M θ).real (s (t + 1) ⁻¹' {y}) := by
    rw [← integral_indicator_one (Random.Measurable.of.All_Eq.snd.fst h₀ (t + 1) (measurableSet_singleton y))]
    refine integral_mono
      (Integrable.of.Measurable (M := M) (fun ω => (s t ω, s (t + 1) ω)) ((Random.Measurable.of.All_Eq.snd.fst h₀ t).prodMk (Random.Measurable.of.All_Eq.snd.fst h₀ (t + 1))) θ
        (fun p => (if p.1 = x then (1:ℝ) else 0) * (if p.2 = y then (1:ℝ) else 0)))
      ((integrable_const (1:ℝ)).indicator (Random.Measurable.of.All_Eq.snd.fst h₀ (t + 1) (measurableSet_singleton y))) (fun ω => ?_)
    by_cases h1 : s t ω = x <;> by_cases h2 : s (t + 1) ω = y <;> simp [h1, h2]
  intro h0
  rw [h0, hE] at hle
  linarith


-- created on 2026-10-07
