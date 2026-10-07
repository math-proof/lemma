import sympy.stats.markov_decision_process
import sympy.Basic
open MeasureTheory ProbabilityTheory


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {MDP : FiniteMDP S A}
-- given
  (y : S × A)
  (s : S)
  (a : A) :
-- imply
  MDP.MRP.P y (s, a) = MDP.P y {s} * MDP.pi s {a} := by
-- proof
  show ((Kernel.compProd MDP.transition_kernel (MDPSpec.pi_kernel₁ MDP.pi)) y {(s, a)}).toReal = _
  rw [← Set.singleton_prod_singleton, Kernel.compProd_apply_prod (measurableSet_singleton s) (measurableSet_singleton a), lintegral_singleton, ENNReal.toReal_mul, mul_comm]
  rfl


-- created on 2026-09-26