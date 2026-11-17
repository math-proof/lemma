/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Contracting

public section

section

open Set

namespace FunctionalAnalysis.BrowderKirkWanted

theorem exists_one_div_succ_lt {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 1 / ((N : ℝ) + 1) < η := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (Iio_mem_nhds hη)
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  exact ⟨N, by have h2 := hN N le_rfl; simpa using h2⟩

theorem one_div_succ_le_of_le {N k : ℕ} (h : N ≤ k) :
    1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
  apply one_div_le_one_div_of_le
  · have hN : (0:ℝ) ≤ (N : ℝ) := by positivity
    linarith
  · have hNk : (N:ℝ) ≤ (k:ℝ) := Nat.cast_le.mpr h
    linarith

end FunctionalAnalysis.BrowderKirkWanted
end
