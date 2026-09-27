import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.StochasticVec.IsClosed


@[main]
private lemma main
  {S : Type*} [Fintype S] :
-- imply
  IsCompact {μ : S → ℝ | StochasticVec μ} := by
-- proof
  refine (isCompact_Icc (a := (0 : S → ℝ)) (b := 1)).of_isClosed_subset StochasticVec.IsClosed fun μ hμ => ⟨fun i => (hμ : StochasticVec μ).nonneg i, fun i => ?_⟩
  have h : StochasticVec μ := hμ
  calc
    _ ≤ ∑ j, μ j := Finset.single_le_sum (fun j _ => h.nonneg j) (Finset.mem_univ i)
    _ = 1 := h.rowsum


-- created on 2026-09-26
