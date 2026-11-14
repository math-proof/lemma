import Lemma.Random.Pnkd0.eq.Eq
import Lemma.Random.PnkdAdd_1.eq.Integral_MulProbIntegral_TPnkd
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
The `1`-step state transition: `Pnkd θ 1 x y = P1kd θ p x y` when `p x u y` is the transition mass `T({y} | x, u)`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : DensityModel Θ 𝒮 𝒜}
  {p : 𝒮 → 𝒜 → 𝒮 → ℝ}
-- given
  (h : ∀ x u y, (M.env.trans (x, u)).real {y} = p x u y)
  (θ : Θ)
  (x y : 𝒮) :
-- imply
  M.Pnkd θ 1 x y = M.P1kd θ p x y := by
-- proof
  have := M.env.trans_markov
  rw [PnkdAdd_1.eq.Integral_MulProbIntegral_TPnkd (M := M) θ 0 x y]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hinter : ∫ y', M.Pnkd θ 0 y' y ∂(M.env.trans (x, u)) =
      (M.env.trans (x, u)).real {y} := by
    have hfun : (fun y' : 𝒮 => M.Pnkd θ 0 y' y) =
        Set.indicator {y} (fun _ => (1:ℝ)) := by
      funext y'
      rw [Pnkd0.eq.Eq]
      by_cases hy' : y' = y <;> simp [Set.indicator, hy']
    rw [hfun, integral_indicator (measurableSet_singleton y), setIntegral_const,
      smul_eq_mul, mul_one, measureReal_def]
  dsimp only
  rw [hinter, h]


-- created on 2026-11-13
