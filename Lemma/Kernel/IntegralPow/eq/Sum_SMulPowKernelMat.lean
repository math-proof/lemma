import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Lemma.Kernel.ToRealPow.eq.PowKernelMat
open MeasureTheory ProbabilityTheory Kernel


@[main]
private lemma main
  [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [NormedAddCommGroup α] [NormedSpace ℝ α] [CompleteSpace α]
  {s : S}
-- given
  (M : HomMarkovChainSpec S)
  (n : ℕ)
  (f : S → α) :
-- imply
  ∫ s', f s' ∂((M.kernel ^ n) s) = ∑ s', (M.kernel_mat ^ n) s s' • f s' := by
-- proof
  have := M.markov_kernel
  rw [integral_fintype (Integrable.of_finite)]
  simp [measureReal_def, ToRealPow.eq.PowKernelMat]


-- created on 2026-09-26