import sympy.stats.markov_chain
open MeasureTheory ProbabilityTheory


@[path]
private lemma main
  [MeasurableSpace S]
-- given
  (M : HomMarkovChainSpec S)
  (s s' : S) :
-- imply
  (M.kernel s {s'}).toReal = M.kernel_mat s s' := by
-- proof
  rfl


-- created on 2026-09-26