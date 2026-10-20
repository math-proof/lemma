import Lemma.Random.Eq_Expect.Eq_Expect.Eq_Expect.of.All_Eq_Expect.All_Eq_Expect.In_Ico
import Lemma.Random.NormV.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.NormQ.le.MulSub1Abs_R.of.In_Ico
open MeasureTheory ProbabilityTheory PolicyGradient Random


/--
py `Random.Le.All_Le_ExpectCondAdd_MulAndAll_Le_ExpectCondAdd_Mul.of.All_Eq.All_Eq.All_Eq_ExpectCondDotPow.All_Eq_ExpectCondDotPow.All_Eq.In_Ico`:
the py `@prove(proved=False)` claims the classical optimal Bellman equalities
\(V^\star=\max_a Q^\star\), \(V^\star=\mathbb E[r+\gamma V^\star\mid s]\),
\(Q^\star=\mathbb E[r+\gamma V^\star\mid s,a]\) with \(Q^\star=\max_\pi Q^\pi\),
\(V^\star=\max_\pi V^\pi\).
Those equalities are false for a general parameterized policy class: e.g. \(\gamma=0\),
one state, two actions with rewards \(0\) and \(1\), and a single mixed policy
\(\pi=(1/2,1/2)\) gives \(V^\star=1/2<\max_a Q^\star=1\), and the \(\exists\theta\)
backup equalities can fail when the \(\sup\) over \(\Theta\) is not attained.
What is true for every policy class (and what we prove) is the one-sided form from
Bellman + monotonicity:
\(V^\star\le\max_a Q^\star\), and for every \(\theta\),
\(V^\theta\le\mathbb E_\theta[r+\gamma V^\star\mid s]\),
\(Q^\theta\le\mathbb E_\theta[r+\gamma V^\star\mid s,a]\).
The on-policy equalities are
`Random.Eq_Expect.Eq_Expect.Eq_Expect.of.All_Eq_Expect.All_Eq_Expect.In_Ico`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [Nonempty A]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ] [Nonempty Θ]
  {M : Model Θ S A}
  {γ : ℝ}
  {t : ℕ}
  {Q : Θ → ℕ → S → A → ℝ}
  {V : Θ → ℕ → S → ℝ}
  {Qstar : ℕ → S → A → ℝ}
  {Vstar : ℕ → S → ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A),
    Q θ t («s.bvar» t) («a.bvar» t) =
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t))
  (h₃ : ∀ θ t («s.bvar» : ℕ → S),
    V θ t («s.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  (hQstar : ∀ t x u, Qstar t x u = ⨆ θ, Q θ t x u)
  (hVstar : ∀ t x, Vstar t x = ⨆ θ, V θ t x)
  («s.bvar» : ℕ → S)
  («a.bvar» : ℕ → A) :
-- imply
  Vstar t («s.bvar» t) ≤ ⨆ u, Qstar t («s.bvar» t) u ∧
    (∀ θ, V θ t («s.bvar» t) ≤
      𝔼[r, s : M θ](r t + γ * Vstar (t + 1) (s (t + 1)) | s t = «s.bvar» t)) ∧
    (∀ θ, Q θ t («s.bvar» t) («a.bvar» t) ≤
      𝔼[r, s : M θ](r t + γ * Vstar (t + 1) (s (t + 1)) |
        s t = «s.bvar» t ∧ a t = «a.bvar» t)) := by
-- proof
  set x := «s.bvar» t
  set u := «a.bvar» t
  have hs : ∀ n, Measurable (s n) := Random.Measurable.of.All_Eq.snd.fst h₁
  have ha : ∀ n, Measurable (a n) := Random.Measurable.of.All_Eq.snd.snd h₁
  have hr : ∀ n, Measurable (r n) := Random.Measurable.of.All_Eq.fst h₁
  have hpa : Measurable (fun ω n ↦ a n ω) := Measurable.of_eval ha
  have hpr : Measurable (fun ω n ↦ r n ω, fun ω n ↦ s n ω) :=
    (Measurable.of_eval hr).prodMk (Measurable.of_eval hs)
  have hVnorm (θ : Θ) (n : ℕ) (y : S) : |V θ n y| ≤ (1 - γ)⁻¹ * |M.env.R| := by
    have := NormV.le.MulSub1Abs_R.of.In_Ico (M := M) h₀ h₁ θ n y
    simp only at this
    rw [← h₃ θ n (fun _ ↦ y)] at this
    exact (Real.norm_eq_abs _).symm ▸ this
  have hQnorm (θ : Θ) (n : ℕ) (y : S) (v : A) : |Q θ n y v| ≤ (1 - γ)⁻¹ * |M.env.R| := by
    have := NormQ.le.MulSub1Abs_R.of.In_Ico (M := M) h₀ h₁ θ n y v
    simp only at this
    rw [← h₂ θ n (fun _ ↦ y) (fun _ ↦ v)] at this
    exact (Real.norm_eq_abs _).symm ▸ this
  have hVbd (n : ℕ) (y : S) : BddAbove (Set.range fun θ : Θ ↦ V θ n y) := by
    refine ⟨(1 - γ)⁻¹ * |M.env.R|, ?_⟩
    rintro _ ⟨θ, rfl⟩
    exact (abs_le.mp (hVnorm θ n y)).2
  have hQbdθ (n : ℕ) (y : S) (v : A) : BddAbove (Set.range fun θ : Θ ↦ Q θ n y v) := by
    refine ⟨(1 - γ)⁻¹ * |M.env.R|, ?_⟩
    rintro _ ⟨θ, rfl⟩
    exact (abs_le.mp (hQnorm θ n y v)).2
  have hVle (θ : Θ) (n : ℕ) (y : S) : V θ n y ≤ Vstar n y := by
    simpa [hVstar] using le_ciSup (hVbd n y) θ
  have hQle (θ : Θ) (n : ℕ) (y : S) (v : A) : Q θ n y v ≤ Qstar n y v := by
    simpa [hQstar] using le_ciSup (hQbdθ n y v) θ
  have hVstarbd (y : S) : |Vstar (t + 1) y| ≤ (1 - γ)⁻¹ * |M.env.R| := by
    rw [hVstar]
    refine abs_le.mpr ⟨?_, ciSup_le fun θ ↦ (abs_le.mp (hVnorm θ (t + 1) y)).2⟩
    exact le_ciSup_of_le (hVbd (t + 1) y) (Classical.arbitrary Θ)
      (abs_le.mp (hVnorm (Classical.arbitrary Θ) (t + 1) y)).1
  have hBellman (θ : Θ) :=
    Eq_Expect.Eq_Expect.Eq_Expect.of.All_Eq_Expect.All_Eq_Expect.In_Ico
      (M := M) (θ := θ) (t := t) (Q := Q θ) (V := V θ) h₀ h₁
      (fun n => h₂ θ n) (fun n => h₃ θ n) «s.bvar» «a.bvar»
  have hpR : Measurable (fun ω n ↦ r n ω) := Measurable.of_eval hr
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) :=
    Measurable.tsum fun k ↦ (measurable_pi_apply (t + k)).const_mul _
  have hQintegral (θ : Θ) (y : S) (v : A) :
    Q θ t y v =
      ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω ∂(M θ)[|(fun ω ↦ (s t ω, a t ω)) ⁻¹' {(y, v)}] := by
    rw [h₂ θ t (fun _ ↦ y) (fun _ ↦ v)]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable hfG]
    rfl
  have hf (W : ℕ → S → ℝ) :
    Measurable (fun integ : (ℕ → ℝ) × (ℕ → S) ↦
      integ.1 t + γ * W (t + 1) (integ.2 (t + 1))) :=
    ((measurable_pi_apply t).comp measurable_fst).add
      (((measurable_of_countable (W (t + 1))).comp
        ((measurable_pi_apply (t + 1)).comp measurable_snd)).const_mul γ)
  have hrae (θ : Θ) : ∀ᵐ ω ∂(M θ), |r t ω| ≤ |M.env.R| := by
    exact (MEq_Clip.of.All_Eq h₁ (M := M) θ t).mono fun ω (heq : r t ω = clip (ω t).1 (-M.env.R) M.env.R) ↦ by
      rw [heq]; exact NormClip.le.AbsR (M := M) _
  have hFcond (θ : Θ) (W : ℕ → S → ℝ)
    (hW : ∀ y, |W (t + 1) y| ≤ (1 - γ)⁻¹ * |M.env.R|)
    {B : Set (ℕ → ℝ × S × A)} :
    Integrable (fun ω ↦ r t ω + γ * W (t + 1) (s (t + 1) ω)) ((M θ)[|B]) := by
    refine Integrable.of_bound
      ((hr t).add
        (((measurable_of_countable (W (t + 1))).comp (hs (t + 1))).const_mul γ)).aestronglyMeasurable
      (|M.env.R| + |γ| * ((1 - γ)⁻¹ * |M.env.R|)) ?_
    refine (cond_absolutelyContinuous (μ := M θ) (s := B)).ae_le ?_
    filter_upwards [hrae θ] with ω hrω
    calc
      _ ≤ ‖r t ω‖ + ‖γ * W (t + 1) (s (t + 1) ω)‖ := norm_add_le _ _
      _ ≤ |M.env.R| + |γ| * ‖W (t + 1) (s (t + 1) ω)‖ := by
        rw [norm_mul, Real.norm_eq_abs γ]
        gcongr
        exact (Real.norm_eq_abs _).trans_le hrω
      _ ≤ |M.env.R| + |γ| * ((1 - γ)⁻¹ * |M.env.R|) := by
        gcongr
        exact (Real.norm_eq_abs _).trans_le (hW (s (t + 1) ω))
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [hVstar]
    refine ciSup_le fun θ ↦ ?_
    obtain ⟨hVQ, -, -⟩ := hBellman θ
    have hQfin : BddAbove (Set.range fun v : A ↦ Q θ t x v) := (Set.finite_range _).bddAbove
    calc
      _ = 𝔼[a : M θ](Q θ t x (a t) | s t = x) := hVQ
      _ ≤ ⨆ v, Q θ t x v := by
        simp only [Expectation.asRV_process]
        rw [Expectation.condEvent_eq_integral hpa.aemeasurable (by fun_prop)]
        if hP : M θ (s t ⁻¹' {x}) = 0 then
          rw [cond_eq_zero_of_meas_eq_zero hP, integral_zero_measure]
          have hQ0 (v : A) : Q θ t x v = 0 := by
            have hPv : M θ ((fun ω ↦ (s t ω, a t ω)) ⁻¹' {(x, v)}) = 0 :=
              measure_mono_null
                (fun ω hω ↦ by
                  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hω ⊢
                  exact hω.1)
                hP
            rw [hQintegral θ x v, cond_eq_zero_of_meas_eq_zero hPv, integral_zero_measure]
          simp [hQ0]
        else
          have : IsProbabilityMeasure ((M θ)[|s t ⁻¹' {x}]) :=
            cond_isProbabilityMeasure hP
          have hQi :
            Integrable (fun ω ↦ Q θ t x (a t ω)) ((M θ)[|s t ⁻¹' {x}]) :=
            Integrable.of_bound
              ((measurable_of_countable (Q θ t x)).comp (ha t)).aestronglyMeasurable
              ((1 - γ)⁻¹ * |M.env.R|)
              (Filter.Eventually.of_forall fun ω ↦
                (Real.norm_eq_abs _).trans_le (hQnorm θ t x (a t ω)))
          refine (integral_mono hQi (integrable_const _) fun ω ↦
            le_ciSup hQfin (a t ω)).trans ?_
          simp
      _ ≤ ⨆ v, Qstar t x v :=
        ciSup_mono (Set.finite_range _).bddAbove fun v ↦ hQle θ t x v
  ·
    intro θ
    obtain ⟨-, hVV, -⟩ := hBellman θ
    calc
      _ = 𝔼[r, s : M θ](r t + γ * V θ (t + 1) (s (t + 1)) | s t = x) := hVV
      _ ≤ 𝔼[r, s : M θ](r t + γ * Vstar (t + 1) (s (t + 1)) | s t = x) := by
        simp only [Expectation.asRV_process]
        rw [Expectation.condEvent_eq_integral hpr.aemeasurable (hf (V θ)),
          Expectation.condEvent_eq_integral hpr.aemeasurable (hf Vstar)]
        apply integral_mono
          (hFcond θ (V θ) fun y ↦ hVnorm θ (t + 1) y)
          (hFcond θ Vstar hVstarbd)
        intro ω
        dsimp only
        gcongr
        · exact h₀.1
        · exact hVle θ (t + 1) (s (t + 1) ω)
  ·
    intro θ
    obtain ⟨-, -, hQQ⟩ := hBellman θ
    calc
      _ = 𝔼[r, s : M θ](r t + γ * V θ (t + 1) (s (t + 1)) | s t = x ∧ a t = u) := hQQ
      _ ≤ 𝔼[r, s : M θ](r t + γ * Vstar (t + 1) (s (t + 1)) | s t = x ∧ a t = u) := by
        simp only [Expectation.asRV_process]
        rw [Expectation.condEvent_eq_integral hpr.aemeasurable (hf (V θ)),
          Expectation.condEvent_eq_integral hpr.aemeasurable (hf Vstar)]
        apply integral_mono
          (hFcond θ (V θ) fun y ↦ hVnorm θ (t + 1) y)
          (hFcond θ Vstar hVstarbd)
        intro ω
        dsimp only
        gcongr
        · exact h₀.1
        · exact hVle θ (t + 1) (s (t + 1) ω)


-- created on 2026-10-12
