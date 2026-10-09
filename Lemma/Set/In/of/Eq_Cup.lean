import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {X : Finset ℝ}
  {y : ℝ}
  {b : ℕ → ℝ}
  {n : ℕ}
-- given
  (h₀ : X \ {y} = (Finset.range n).biUnion (fun k ↦ ({b k} : Finset ℝ)))
  (h₁ : X.card = n + 1) :
-- imply
  y ∈ X := by
-- proof
  by_contra h
  have h₂ : X \ {y} = X := Finset.sdiff_eq_self_iff_disjoint.mpr (Finset.disjoint_singleton_right.mpr h)
  rw [h₂] at h₀
  have h₃ : X.card ≤ n := calc
    _ = ((Finset.range n).biUnion fun k ↦ ({b k} : Finset ℝ)).card := by rw [h₀]
    _ ≤ ∑ k ∈ Finset.range n, ({b k} : Finset ℝ).card := Finset.card_biUnion_le
    _ = n := by simp
  omega


-- created on 2021-03-22
