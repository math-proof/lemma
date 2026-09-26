import sympy.stats.q_learning
import sympy.Basic
import Lemma.QLearningSpec.ContractingWithBellmanOp


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A]
  {spec : QLearningSpec S A} :
-- imply
  spec.bellman_op (WithLp.ofLp spec.optimal_q) = WithLp.ofLp spec.optimal_q :=
-- proof
  Classical.epsilon_spec (p := fun q => spec.bellman_op q = q) ⟨_, ContractingWith.fixedPoint_isFixedPt (f := spec.bellman_op) QLearningSpec.ContractingWithBellmanOp⟩


-- created on 2026-09-26
