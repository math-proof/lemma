import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Lemma.Random.ProbJoint.eq.Mul_Prod_MulProbSCond.of.IsDiscreteHMM
open MeasureTheory Random
open scoped ENNReal.ToRealCoe


/--
Policy gradient theorem (log-derivative trick) for a Markov decision process with weights `θ`.
Let `s i` be the states and `a i` the actions (discrete, counting reference measures) under the
trajectory law `π θ`, where the weights `θ` only enter through the policy `ℙ(a[t] | s[t])`: the initial
law `ℙ(s[0])` and the transition law `ℙ(s[t + 1] | s[t] ∧ a[t])` do not depend on `θ` (`hinit`,
`htr`).  The Markov property says that the action depends on the history only through the current
state (`hpol`) and the next state only through the current state and action (`htrans`).  If the
trajectory has nonzero probability, then

  `∇[θ] log ℙ(s[:T + 1] = sv[:T + 1] ∧ a[:T] = av[:T]) = ∑ t < T, ∇[θ] log ℙ(a[t] = av[t] | s[t] = sv[t])`.

The factorization `ℙ(s[:T + 1], a[:T]) = C * ∏ t < T, ℙ(a[t] | s[t])`, with `C` independent of `θ`, is
derived (`Random.ProbJoint.eq.Mul_Prod_MulProbSCond.of.IsDiscreteHMM.mdp`), not assumed.

Python: Tensor.Eq.of.Ne_0.Eq.Eq.Eq.policy_gradient_theorem.
-/
@[path]
private lemma policy_gradient_theorem
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [CountableMeasure S] [CountableMeasure A]
  [Countable S] [MeasurableSingletonClass S] [Countable A] [MeasurableSingletonClass A]
  {π : E → Measure Ω} {s : ℕ → Ω → S} {a : ℕ → Ω → A} [∀ θ, IsProbabilityMeasure (π θ)] [∀ θ i, SinglePSpace (π θ) (s i)] [∀ θ i j, SinglePSpace (π θ) (a i, s j)] [∀ θ i, SinglePSpace (π θ) (s (i + 1), s i, a i)] [∀ θ n, SinglePSpace (π θ) (s[:n + 1], a[:n])]
  {T : ℕ} {sv : ℕ → S} {av : ℕ → A}
-- given
  (hs : ∀ k, Measurable (s k))
  (ha : ∀ k, Measurable (a k))
  (hpol : ∀ θ t, ∀ _ : Measurable (s t),
    a t ⟂ᵢ[π θ] (s[:t], a[:t]) | s t)
  (htrans : ∀ θ t, ∀ _ : Measurable (s t, a t),
    s (t + 1) ⟂ᵢ[π θ] (s[:t], a[:t]) | (s t, a t))
  (hinit : ∀ θ θ', (ℙ[π θ]((s 0) = sv 0) : ℝ) = (ℙ[π θ']((s 0) = sv 0) : ℝ))
  (htr : ∀ θ θ' i, (ℙ[π θ]((s (i + 1)) = sv (i + 1) | (s i) = sv i ∧ (a i) = av i) : ℝ) =
    (ℙ[π θ']((s (i + 1)) = sv (i + 1) | (s i) = sv i ∧ (a i) = av i) : ℝ))
  (hne : ∀ θ, 0 < (ℙ[π θ](s[:T + 1] = sv[:T + 1] ∧ a[:T] = av[:T]) : ℝ))
  (hdiff : ∀ θ t, DifferentiableAt ℝ (fun θ => (ℙ[π θ]((a t) = av t | (s t) = sv t) : ℝ)) θ) :
-- imply
  ∀ θ₀ : E, fderiv ℝ (fun θ => (ℙ[π θ](s[:T + 1] = sv[:T + 1] ∧ a[:T] = av[:T]) : ℝ).log) θ₀ = ∑ t ∈ Finset.range T, fderiv ℝ (fun θ => (ℙ[π θ]((a t) = av t | (s t) = sv t) : ℝ).log) θ₀ := by
-- proof
  intro θ₀
  obtain ⟨p, hp⟩ : ∃ p : E → ℕ → ℝ, ∀ θ t, p θ t = (ℙ[π θ]((a t) = av t | (s t) = sv t) : ℝ) :=
    ⟨fun θ t => (ℙ[π θ]((a t) = av t | (s t) = sv t) : ℝ), fun _ _ => rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (ℙ[π θ₀]((s 0) = sv 0) : ℝ) *
      ∏ i ∈ Finset.range T, (ℙ[π θ₀]((s (i + 1)) = sv (i + 1) | (s i) = sv i ∧ (a i) = av i) : ℝ) :=
    ⟨_, rfl⟩
  have hfac : ∀ θ, (ℙ[π θ](s[:T + 1] = sv[:T + 1] ∧ a[:T] = av[:T]) : ℝ) = C * ∏ t ∈ Finset.range T, p θ t := by
    intro θ
    have h := ProbJoint.eq.Mul_Prod_MulProbSCond.of.IsDiscreteHMM.mdp (π := π θ)
      («s.bvar» := sv) («a.bvar» := av) hs ha (hpol θ) (htrans θ) T
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_prod]
    simp only [ENNReal.toReal_mul]
    rw [Finset.prod_mul_distrib, hC, hinit θ θ₀, mul_assoc]
    congr 1
    rw [mul_comm]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => htr θ θ₀ i
    · exact Finset.prod_congr rfl fun i _ => (hp θ i).symm
  have hCnn : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg ENNReal.toReal_nonneg (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)
  have hpnn : ∀ θ t, 0 ≤ p θ t := fun θ t =>
    hp θ t ▸ ENNReal.toReal_nonneg
  have hCpos : 0 < C := by
    refine lt_of_le_of_ne hCnn fun h => ?_
    have := hne θ₀
    rw [hfac θ₀, ← h, zero_mul] at this
    exact lt_irrefl _ this
  have hppos : ∀ θ, ∀ t ∈ Finset.range T, 0 < p θ t := by
    intro θ t ht
    refine lt_of_le_of_ne (hpnn θ t) fun h => ?_
    have := hne θ
    rw [hfac θ, Finset.prod_eq_zero ht h.symm, mul_zero] at this
    exact lt_irrefl _ this
  have hdiff' : ∀ θ t, DifferentiableAt ℝ (fun θ => p θ t) θ := fun θ t => by
    simpa only [hp] using hdiff θ t
  have e : (fun θ => (ℙ[π θ](s[:T + 1] = sv[:T + 1] ∧ a[:T] = av[:T]) : ℝ).log) =
      fun θ => C.log + ∑ t ∈ Finset.range T, (p θ t).log := by
    funext θ
    rw [hfac θ, Real.log_mul hCpos.ne' (Finset.prod_pos (hppos θ)).ne',
      Real.log_prod (fun t ht => (hppos θ t ht).ne')]
  rw [e, fderiv_const_add, fderiv_fun_sum (fun t ht => (hdiff' θ₀ t).log (hppos θ₀ t ht).ne')]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [hp]


-- created on 2023-03-22
-- updated on 2026-10-23