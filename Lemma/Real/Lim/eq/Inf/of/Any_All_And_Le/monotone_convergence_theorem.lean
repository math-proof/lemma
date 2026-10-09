import Mathlib.Topology.Order.MonotoneConvergence
import sympy.series.limits
import sympy.sets.sets
import sympy.Basic
import Lemma.Real.Lim.eq.Inf.of.Le.Any_All_Ge.monotone_convergence_theorem




@[path]
private lemma main
  {a : ℕ → ℝ}
-- given
  (h : ∃ M, ∀ n, M ≤ a (n + 1) ∧ a (n + 1) ≤ a n) :
-- imply
  lim [n → ∞] a n = sInf (Set.range a) := by
-- proof
  obtain ⟨M, hM⟩ := h
  have hle : ∀ n, a (n + 1) ≤ a n := fun n => (hM n).2
  have hge : ∀ n, M ≤ a n := by
    intro n
    cases n with
    | zero => exact le_trans (hM 0).1 (hle 0)
    | succ n => exact (hM n).1
  exact Real.Lim.eq.Inf.of.Le.Any_All_Ge.monotone_convergence_theorem hle ⟨M, hge⟩


-- created on 2024-06-27
