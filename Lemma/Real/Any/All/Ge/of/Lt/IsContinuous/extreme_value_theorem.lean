import Mathlib.Topology.Order.Compact
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
  -- given
  (hlt : a < b)
  (hcont : ContinuousOn f (Set.Icc a b))
  -- imply
  : ∃ xi ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b, f xi ≤ f z := by
  -- proof
  have hle : a ≤ b := le_of_lt hlt
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hne : Set.Nonempty (Set.Icc a b) := Set.nonempty_Icc.mpr hle
  rcases hcompact.exists_isMinOn hne hcont with ⟨xi, hxi, hmin⟩
  refine ⟨xi, hxi, fun z hz => hmin hz⟩

-- created on 2023-10-15
-- updated on 2023-11-10
