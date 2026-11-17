import Lemma.Random.Pnkd0.eq.Eq
import Lemma.Random.Pnkd1.eq.P1kd.of.All_EqReal
import Lemma.Random.PnkdAdd_1.eq.Integral_MulProbIntegral_TPnkd
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


private lemma pnkd_step_sum
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  (θ : Θ) (n : ℕ) (sₜ y : 𝒮) :
  M.Pnkd θ (n + 1) sₜ y =
    ∫ u, M.π[θ] sₜ u *
      ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} * M.Pnkd θ n y' y
      ∂ReferenceMeasure.measure := by
  rw [PnkdAdd_1.eq.Integral_MulProbIntegral_TPnkd (M := M) θ n sₜ y]
  congr 1
  funext u
  congr 1
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [smul_eq_mul, measureReal_def]


private lemma integrable_prob_mul_sum
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  (θ : Θ) (n : ℕ) (sₜ y : 𝒮) :
  Integrable
    (fun u => M.π[θ] sₜ u *
      ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} * M.Pnkd θ n y' y)
    ReferenceMeasure.measure := by
  have hπ : Integrable (M.π[θ] sₜ) ReferenceMeasure.measure :=
    integrable_of_integral_eq_one (hStoch.integral_eq_one θ sₜ)
  have hTmeas : ∀ y', Measurable fun u => (M.trans (sₜ, u)).toMeasure.real {y'} :=
    fun y' =>
      ((M.transK.measurable_coe (measurableSet_singleton y')).comp
        measurable_prodMk_left).ennreal_toReal
  have hg : Measurable fun u =>
      ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} * M.Pnkd θ n y' y :=
    Finset.measurable_fun_sum Finset.univ fun y' _ => (hTmeas y').mul measurable_const
  let C : ℝ := ∑ y' : 𝒮, ‖M.Pnkd θ n y' y‖
  have hble : ∀ u,
      ‖∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} * M.Pnkd θ n y' y‖ ≤ C := by
    intro u
    calc
      ‖∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} * M.Pnkd θ n y' y‖
        ≤ ∑ y', ‖(M.trans (sₜ, u)).toMeasure.real {y'} * M.Pnkd θ n y' y‖ :=
          norm_sum_le Finset.univ _
      _ ≤ ∑ y', ‖M.Pnkd θ n y' y‖ := by
        refine Finset.sum_le_sum fun y' _ => ?_
        rw [norm_mul]
        have hTle : ‖(M.trans (sₜ, u)).toMeasure.real {y'}‖ ≤ (1:ℝ) := by
          have hnn : 0 ≤ (M.trans (sₜ, u)).toMeasure.real {y'} := measureReal_nonneg
          have hle : (M.trans (sₜ, u)).toMeasure.real {y'} ≤ 1 := by
            have huniv : (M.trans (sₜ, u)).toMeasure.real Set.univ = 1 := by
              rw [measureReal_def, measure_univ, ENNReal.toReal_one]
            rw [← huniv]
            exact measureReal_mono (Set.subset_univ {y'})
          rwa [Real.norm_of_nonneg hnn]
        exact mul_le_of_le_one_left (norm_nonneg _) hTle
      _ = C := rfl
  have hbound : Integrable (fun u => C * ‖M.π[θ] sₜ u‖) ReferenceMeasure.measure :=
    hπ.norm.const_mul C
  refine Integrable.mono' hbound
    (hπ.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u => ?_)
  simp only [norm_mul]
  rw [mul_comm C]
  exact mul_le_mul_of_nonneg_left (hble u) (norm_nonneg _)


/--
Chapman–Kolmogorov: `ℙ(s[n+1] = z | s[0] = x) = ∑ y, ℙ(s[n] = y | s[0] = x) * ℙ(s[1] = z | s[0] = y)`,
for the continuous-action n-step transition `Pnkd` and the one-step kernel `P1kd`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {p : 𝒮 → 𝒜 → 𝒮 → ℝ}
-- given
  (h : ∀ x u y, (M.trans (x, u)).toMeasure.real {y} = p x u y)
  (θ : Θ)
  (n : ℕ)
  (sₜ z : 𝒮) :
-- imply
  M.Pnkd θ (n + 1) sₜ z = ∑ y, M.Pnkd θ n sₜ y * M.P1kd θ p y z := by
-- proof
  induction n generalizing sₜ with
  | zero =>
    rw [Pnkd1.eq.P1kd.of.All_EqReal (M := M) h θ sₜ z]
    simp [Pnkd0.eq.Eq]
  | succ n ih =>
    have hI : ∀ y, Integrable
        (fun u => M.π[θ] sₜ u *
          ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} * M.Pnkd θ n y' y)
        ReferenceMeasure.measure :=
      fun y => integrable_prob_mul_sum (M := M) θ n sₜ y
    have hI2 : ∀ y, Integrable
        (fun u => M.π[θ] sₜ u *
          ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} *
            (M.Pnkd θ n y' y * M.P1kd θ p y z))
        ReferenceMeasure.measure := by
      intro y
      simpa [mul_assoc, Finset.sum_mul] using
        (hI y).mul_const (M.P1kd θ p y z)
    calc
      M.Pnkd θ (n + 1 + 1) sₜ z
        = ∫ u, M.π[θ] sₜ u *
            ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} * M.Pnkd θ (n + 1) y' z
            ∂ReferenceMeasure.measure :=
          pnkd_step_sum (M := M) θ (n + 1) sₜ z
      _ = ∫ u, M.π[θ] sₜ u *
            ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} *
              ∑ y, M.Pnkd θ n y' y * M.P1kd θ p y z
            ∂ReferenceMeasure.measure := by
        congr 1
        funext u
        simp_rw [ih]
      _ = ∫ u, ∑ y, M.π[θ] sₜ u *
            ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} *
              (M.Pnkd θ n y' y * M.P1kd θ p y z)
            ∂ReferenceMeasure.measure := by
        congr 1
        funext u
        calc
          M.π[θ] sₜ u *
            ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} *
              ∑ y, M.Pnkd θ n y' y * M.P1kd θ p y z
            = ∑ y', M.π[θ] sₜ u *
                ((M.trans (sₜ, u)).toMeasure.real {y'} *
                  ∑ y, M.Pnkd θ n y' y * M.P1kd θ p y z) := by
              simp [Finset.mul_sum]
          _ = ∑ y', ∑ y, M.π[θ] sₜ u *
                ((M.trans (sₜ, u)).toMeasure.real {y'} *
                  (M.Pnkd θ n y' y * M.P1kd θ p y z)) := by
              refine Finset.sum_congr rfl fun y' _ => ?_
              simp [Finset.mul_sum]
          _ = ∑ y, ∑ y', M.π[θ] sₜ u *
                ((M.trans (sₜ, u)).toMeasure.real {y'} *
                  (M.Pnkd θ n y' y * M.P1kd θ p y z)) :=
              Finset.sum_comm
          _ = ∑ y, M.π[θ] sₜ u *
                ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} *
                  (M.Pnkd θ n y' y * M.P1kd θ p y z) := by
              refine Finset.sum_congr rfl fun y _ => ?_
              simp [Finset.mul_sum]
      _ = ∑ y, ∫ u, M.π[θ] sₜ u *
            ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} *
              (M.Pnkd θ n y' y * M.P1kd θ p y z)
            ∂ReferenceMeasure.measure :=
        integral_finsetSum _ (fun y _ => hI2 y)
      _ = ∑ y, (∫ u, M.π[θ] sₜ u *
            ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} * M.Pnkd θ n y' y
            ∂ReferenceMeasure.measure) * M.P1kd θ p y z := by
        refine Finset.sum_congr rfl fun y _ => ?_
        have hfun :
            (fun u => M.π[θ] sₜ u *
              ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} *
                (M.Pnkd θ n y' y * M.P1kd θ p y z)) =
            fun u =>
              (M.π[θ] sₜ u *
                ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} * M.Pnkd θ n y' y) *
                M.P1kd θ p y z := by
          funext u
          simp [mul_assoc, Finset.sum_mul]
        rw [hfun]
        simpa [smul_eq_mul] using
          integral_smul_const
            (f := fun u => M.π[θ] sₜ u *
              ∑ y', (M.trans (sₜ, u)).toMeasure.real {y'} * M.Pnkd θ n y' y)
            (c := M.P1kd θ p y z)
      _ = ∑ y, M.Pnkd θ (n + 1) sₜ y * M.P1kd θ p y z := by
        simp_rw [← pnkd_step_sum (M := M) θ n sₜ]


-- created on 2026-11-13
-- updated on 2026-11-16
