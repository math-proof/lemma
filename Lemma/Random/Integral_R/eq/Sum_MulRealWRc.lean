import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.RealPreimageS0.eq.Real
import Lemma.Real.Sum_Eq.eq.One
import Lemma.Random.Integrable_Mul_R.of.Measurable
import Lemma.Random.Integral_MulEqSR_Add.eq.MulRealPreimageSWRc
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
Expected reward of the trajectory model: `𝔼[r[t]] = ∑ x, init {x} * W θ rc t x` (`rc` the clamped reward).
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (t : ℕ) :
-- imply
  ∫ ω, reward t ω ∂(M θ) = ∑ x, M.env.init.real {x} * M.W θ M.rc t x := by
-- proof
  have h₁ : ∀ ω : ℕ → ℝ × S × A, reward t ω = ∑ x, (if state 0 ω = x then (1:ℝ) else 0) * reward (0 + t) ω := by
    intro ω
    rw [← Finset.sum_mul, Real.Sum_Eq.eq.One, one_mul, zero_add]
  simp_rw [h₁]
  rw [integral_finsetSum _ (fun x _ => Integrable_Mul_R.of.Measurable (M := M) (state 0) (Random.Measurable_S 0) θ
    (fun y => if y = x then (1:ℝ) else 0) (0 + t))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Integral_MulEqSR_Add.eq.MulRealPreimageSWRc (M := M) θ 0 t x, RealPreimageS0.eq.Real]


-- created on 2026-10-06
