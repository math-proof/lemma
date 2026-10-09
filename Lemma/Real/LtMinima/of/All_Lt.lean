import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {α : Type*}
  {S : Set α}
  {f : α → ℝ}
  {M : ℝ}
-- given
  (hS : S.Nonempty)
  (hB : BddBelow (f '' S))
  (h : ∀ x ∈ S, f x < M) :
-- imply
  Minima S f < M := by
-- proof
  obtain ⟨x, hx⟩ := hS
  have hle : Minima S f ≤ f x :=
    csInf_le hB (Set.mem_image_of_mem f hx)
  exact hle.trans_lt (h x hx)


-- created on 2023-03-25
