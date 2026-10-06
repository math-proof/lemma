import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {α : Type*}
  {S : Set α}
  {f : α → ℝ}
  {M : ℝ}
-- given
  (hB : BddAbove (f '' S))
  (h : Maxima S f < M) :
-- imply
  ∀ x ∈ S, f x < M := by
-- proof
  intro x hx
  have hle : f x ≤ Maxima S f :=
    le_csSup hB (Set.mem_image_of_mem f hx)
  exact hle.trans_lt h


-- created on 2023-11-12
