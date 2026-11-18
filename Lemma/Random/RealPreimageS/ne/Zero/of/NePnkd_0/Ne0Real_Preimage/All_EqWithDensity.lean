import Lemma.Random.Pnkd0.eq.Eq
import Lemma.Random.PnkdAdd_1.eq.Integral_MulProbIntegral_TPnkd
import Lemma.Random.RealPreimageS.eq.Sum_MulRealPn.of.All_EqWithDensity
import Lemma.Random.RealPreimageS0.eq.Real.of.All_EqWithDensity
import Lemma.Random.Pnkd.eq.Integral
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


private lemma Pnkd_nonneg
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ)
  (n : ℕ)
  (sₜ y : 𝒮) :
-- imply
  0 ≤ M.Pnkd θ n sₜ y := by
-- proof
  induction n generalizing sₜ with
  | zero =>
    rw [Pnkd0.eq.Eq]
    split_ifs <;> norm_num
  | succ n ih =>
    rw [PnkdAdd_1.eq.Integral_MulProbIntegral_TPnkd]
    exact integral_nonneg fun u =>
      mul_nonneg (hStoch.nonneg θ sₜ u) (integral_nonneg fun y' => ih y')

/--
If `s[0] = x` is reachable and `Pnkd θ n x y ≠ 0`, then `s[n] = y` is reachable.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {n : ℕ}
  {sₜ y : 𝒮}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (h₁ : (M θ).real (s 0 ⁻¹' {sₜ}) ≠ 0)
  (h₂ : M.Pnkd θ n sₜ y ≠ 0) :
-- imply
  (M θ).real (s n ⁻¹' {y}) ≠ 0 := by
-- proof
  rw [RealPreimageS.eq.Sum_MulRealPn.of.All_EqWithDensity h₀]
  simp_rw [← Pnkd.eq.Integral (M := M) θ n _ y]
  rw [RealPreimageS0.eq.Real.of.All_EqWithDensity h₀] at h₁
  refine ne_of_gt (lt_of_lt_of_le ?_ (Finset.single_le_sum
    (f := fun x' => M.init.toMeasure.real {x'} * M.Pnkd θ n x' y)
    (fun x' _ => mul_nonneg measureReal_nonneg (Pnkd_nonneg θ n x' y)) (Finset.mem_univ sₜ)))
  exact mul_pos (lt_of_le_of_ne measureReal_nonneg (Ne.symm h₁))
    (lt_of_le_of_ne (Pnkd_nonneg θ n sₜ y) (Ne.symm h₂))


-- created on 2026-11-13
-- updated on 2026-11-18