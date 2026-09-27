import sympy.stats.markov_chain
import sympy.Basic
open MeasureTheory ProbabilityTheory


@[main]
private lemma main
  [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
-- given
  (M : HomMarkovChainSpec S)
  (n : ℕ)
  (s s' : S) :
-- imply
  ((M.kernel ^ n) s {s'}).toReal = (M.kernel_mat ^ n) s s' := by
-- proof
  have := M.markov_kernel
  induction n generalizing s' with
  | zero =>
    rw [pow_zero, pow_zero, Matrix.one_apply]
    show (Kernel.id s {s'}).toReal = _
    rw [Kernel.id_apply, Measure.dirac_apply]
    simp [Set.indicator_apply, apply_ite ENNReal.toReal]
  | succ n ih =>
    rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ (measurableSet_singleton s'), lintegral_fintype,
      ENNReal.toReal_sum fun l _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _),
      pow_succ, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ENNReal.toReal_mul, ih, mul_comm]
    rfl


-- created on 2026-09-26