import sympy.stats.q_learning
import sympy.Basic
import Lemma.Matrix.All_Gt_0.of.Stationary.StochasticIrreducible
open Finset


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {spec : QLearningSpec S A} :
-- imply
  0 < spec.μmin ∧ 0 ≤ spec.η ∧ spec.η < 1 := by
-- proof
  have hμ : StochasticVec spec.MRP.μ := inferInstance
  have hpos := Matrix.All_Gt_0.of.Stationary.StochasticIrreducible (μ := spec.MRP.μ) (P := spec.MRP.P) inferInstance inferInstance
  have hγ := spec.hγ
  obtain ⟨y, -, hy⟩ := exists_mem_eq_inf' (univ_nonempty (α := S × A)) spec.MRP.μ
  have h₀ : 0 < spec.μmin := (lt_inf'_iff _).2 fun y _ => hpos y
  have h₁ : spec.μmin ≤ 1 := by
    rw [QLearningSpec.μmin, hy, ← hμ.rowsum]
    exact single_le_sum (fun y _ => hμ.nonneg y) (mem_univ y)
  refine ⟨h₀, ?_, ?_⟩ <;> unfold QLearningSpec.η <;> nlinarith


-- created on 2026-09-26
