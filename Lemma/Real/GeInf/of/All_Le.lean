import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {m : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h : ∀ x ∈ S, m ≤ f x) :
-- imply
  sInf (f '' S) ≥ m := by
-- proof
  exact le_csInf (h₀.image f)
    (Set.forall_mem_image.mpr fun x hx => h x hx)


-- created on 2019-01-24
-- updated on 2023-04-14
