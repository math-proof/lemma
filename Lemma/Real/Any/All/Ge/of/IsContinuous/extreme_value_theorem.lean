import Mathlib.Topology.Order.Compact
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
  -- given
  (hcont : ContinuousOn f (Set.Icc a b))
  (hle : a ≤ b)
  -- imply
  : ∃ xi ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b, f xi ≤ f z := by
  -- proof
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hne : Set.Nonempty (Set.Icc a b) := Set.nonempty_Icc.mpr hle
  rcases hcompact.exists_isMinOn hne hcont with ⟨xi, hxi, hmin⟩
  refine ⟨xi, hxi, fun z hz => hmin hz⟩

-- created on 2020-06-13
-- updated on 2023-10-15
