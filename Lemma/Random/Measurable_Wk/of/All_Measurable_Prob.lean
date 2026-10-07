import sympy.stats.policy_trajectory.continuous
import sympy.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Lemma.Random.MeasurableRk
open MeasureTheory PolicyGradient Random


/--
If every `x ↦ π_θ(u | x)` is measurable, so is the `k`-step expected reward `x ↦ Wk θ k x = 𝔼[r[t+k] | s[t] = x]`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (h : ∀ θ u, Measurable (fun x => M.pol.prob θ x u))
  (θ : Θ)
  (k : ℕ) :
-- imply
  Measurable (M.Wk θ k) := by
-- proof
  induction k with
  | zero =>
    apply Finset.measurable_sum _ fun u _ => (h θ u).mul (MeasurableRk (M := M) u)
  | succ k ih =>
    have := M.env.trans_markov
    refine Finset.measurable_sum _ fun u _ => (h θ u).mul ?_
    apply (StronglyMeasurable.integral_kernel_prod_right (κ := M.env.trans.comap (fun x => (x, u)) (by fun_prop))
      (f := fun (_ : S) y => M.Wk θ k y) (ih.stronglyMeasurable.comp_measurable measurable_snd)).measurable


-- created on 2026-10-07
