import Mathlib.Topology.Order.OrderClosed
import sympy.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {a b A B : ℝ}
-- given
  (h₀ : a < b)
  (h₁ : ∀ x ∈ Set.Ioo a b, g x < f x)
  (h₂ : Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds A))
  (h₃ : Filter.Tendsto g (nhdsWithin b (Set.Iio b)) (nhds B)) :
-- imply
  B ≤ A := by
-- proof
  have hmem : Set.Ioo a b ∈ nhdsWithin b (Set.Iio b) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Ioi a, isOpen_Ioi.mem_nhds h₀, fun x hx => hx⟩
  apply le_of_tendsto_of_tendsto h₃ h₂
  filter_upwards [hmem] with x hx
  exact (h₁ x hx).le


-- created on 2026-10-11
-- updated on 2026-10-17
