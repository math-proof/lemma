import sympy.stats.markov_chain_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory Finset


@[main]
private lemma main
  [MeasurableSpace S]
-- given
  (M : HomMarkovChainSpec S) :
-- imply
  (M.traj_prob : Measure (ℕ → S)) = ((M.init : Measure S).map fun s (_ : Iic 0) => s).bind (Kernel.traj (X := fun _ => S) M.expand_kernel 0) := by
-- proof
  rfl


-- created on 2026-09-26