import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Bernoulli
import Initialize.Tactic.Attr.Basic
open ProbabilityTheory


/--
Sum of two i.i.d. Bernoulli random variables is binomial with two trials:
the point masses of `Bin(2, p)` factor through `Ber(1, 0, p)`.
-/
@[path]
private lemma main
  (p : unitInterval) :
-- imply
  (binomial 2 p).real {0} =
      (bernoulliMeasure 1 0 p).real {0} * (bernoulliMeasure 1 0 p).real {0} ∧
    (binomial 2 p).real {2} =
      (bernoulliMeasure 1 0 p).real {1} * (bernoulliMeasure 1 0 p).real {1} ∧
    (binomial 2 p).real {1} =
      (bernoulliMeasure 1 0 p).real {1} * (bernoulliMeasure 1 0 p).real {0} +
        (bernoulliMeasure 1 0 p).real {0} * (bernoulliMeasure 1 0 p).real {1} := by
-- proof
  refine ⟨?_, ?_, ?_⟩
  · simp [binomial_real_singleton, bernoulliMeasure_real_apply_of_notMem_of_mem, pow_two]
  · simp [binomial_real_self, bernoulliMeasure_real_apply_of_mem_of_notMem, pow_two]
  ·
    simp [binomial_real_singleton, bernoulliMeasure_real_apply_of_mem_of_notMem,
      bernoulliMeasure_real_apply_of_notMem_of_mem]
    ring


-- created on 2021-07-17
-- updated on 2026-10-26
