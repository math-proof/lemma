import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.OrderClosed
import sympy.stats.generator_matrix
import sympy.Basic


@[main]
private lemma main
  {S : Type*} [Fintype S] :
-- imply
  IsClosed {μ : S → ℝ | StochasticVec μ} := by
-- proof
  have h : {μ : S → ℝ | StochasticVec μ} = (⋂ s, {μ | 0 ≤ μ s}) ∩ {μ | ∑ s, μ s = 1} := by
    ext μ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨h.nonneg, h.rowsum⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [h]
  exact (isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)).inter
    (isClosed_eq (continuous_finsetSum _ fun s _ => continuous_apply s) continuous_const)


-- created on 2026-09-26
