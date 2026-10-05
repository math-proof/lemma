import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {m : ℝ}
-- given
  (_h₀ : S.Nonempty)
  (hB : BddBelow (f '' S))
  (h : sInf (f '' S) ≥ m) :
-- imply
  ∀ x ∈ S, f x ≥ m := by
-- proof
  intro x hx
  exact le_trans h (csInf_le hB (Set.mem_image_of_mem f hx))


-- created on 2026-10-03
