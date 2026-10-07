import Mathlib.Topology.Order.Compact
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
  -- given
  (hcont : ContinuousOn f (Set.Icc a b))
  (_hle : a ≤ b)
  -- imply
  : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, f x ≤ M := by
  -- proof
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hbdd : BddAbove (f '' Set.Icc a b) := hcompact.bddAbove_image hcont
  rcases hbdd with ⟨M, hM⟩
  refine ⟨M, fun x hx => hM (Set.mem_image_of_mem f hx)⟩

-- created on 2020-06-13
