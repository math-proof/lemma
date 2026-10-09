import Mathlib.Topology.Order.MonotoneConvergence
import sympy.series.limits
import sympy.sets.sets
import sympy.Basic
import Lemma.Real.Lim.eq.Sup.of.Ge.Any_All_Le.monotone_convergence_theorem




@[path]
private lemma main
  {a : ℕ → ℝ}
-- given
  (h : ∃ M, ∀ n, a (n + 1) ≤ M ∧ a n ≤ a (n + 1)) :
-- imply
  lim [n → ∞] a n = sSup (Set.range a) := by
-- proof
  obtain ⟨M, hM⟩ := h
  have hge : ∀ n, a n ≤ a (n + 1) := fun n => (hM n).2
  have hle : ∀ n, a n ≤ M := by
    intro n
    cases n with
    | zero => exact le_trans (hge 0) (hM 0).1
    | succ n => exact (hM n).1
  exact Real.Lim.eq.Sup.of.Ge.Any_All_Le.monotone_convergence_theorem hge ⟨M, hle⟩


-- created on 2024-06-27
