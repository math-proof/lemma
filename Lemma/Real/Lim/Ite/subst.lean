import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Order.Basic
import sympy.Basic


@[path]
private lemma main
  {f g : ℕ → ℝ} {a : ℤ} {L : ℝ} :
-- imply
  Filter.Tendsto (fun n : ℕ => if a < (n : ℤ) then f n else g n) Filter.atTop (nhds L) ↔
    Filter.Tendsto f Filter.atTop (nhds L) := by
-- proof
  apply Filter.tendsto_congr'
  obtain ⟨N, hN⟩ : ∃ N : ℕ, a < (N : ℤ) := by
    refine ⟨(a.natAbs + 1), ?_⟩
    have : (a : ℤ) < (a.natAbs + 1 : ℕ) := by
      cases a with
      | ofNat n =>
        simp
      | negSucc n =>
        simp
        omega
    simpa using this
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  have hlt : a < (n : ℤ) := by
    have hNle : (N : ℤ) ≤ n := by exact_mod_cast hn
    linarith
  simp [hlt]


-- created on 2026-10-11
-- updated on 2026-10-17
