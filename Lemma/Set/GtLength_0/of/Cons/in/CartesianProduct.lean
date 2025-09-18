import Lemma.Algebra.CartesianProductNil.eq.ListNil
open Algebra


@[main]
private lemma main
  {x₀ : ℕ}
  {x s : List ℕ}
-- given
  (h : (x₀ :: x) ∈ s.cartesianProduct) :
-- imply
  s.length > 0 := by
-- proof
  by_contra h'
  simp at h'
  rw [h'] at h
  rw [CartesianProductNil.eq.ListNil] at h
  simp at h


-- created on 2025-06-14
