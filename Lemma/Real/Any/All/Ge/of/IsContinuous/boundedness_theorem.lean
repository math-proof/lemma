import Mathlib.Topology.Order.Compact
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
  -- given
  (hcont : ContinuousOn f (Set.Icc a b))
  (_hle : a ≤ b)
  -- imply
  : ∃ m : ℝ, ∀ x ∈ Set.Icc a b, m ≤ f x := by
  -- proof
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hbdd : BddBelow (f '' Set.Icc a b) := hcompact.bddBelow_image hcont
  rcases hbdd with ⟨m, hm⟩
  refine ⟨m, fun x hx => ?_⟩
  exact hm (Set.mem_image_of_mem f hx)

-- created on 2020-06-13
