import sympy.stats.q_learning
import sympy.Basic
import Lemma.QLearningSpec.NormSubBellmanOp.le.MulNormSub


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A]
  {spec : QLearningSpec S A} :
-- imply
  ContractingWith spec.γ.toNNReal spec.bellman_op :=
-- proof
  ⟨Real.toNNReal_lt_one.2 spec.hγ.2, lipschitzWith_iff_norm_sub_le.2 fun q q' => by rw [Real.coe_toNNReal _ spec.hγ.1]; exact QLearningSpec.NormSubBellmanOp.le.MulNormSub q q'⟩


-- created on 2026-09-26
