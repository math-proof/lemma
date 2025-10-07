import Lemma.Algebra.GeSumS.of.All_Ge
open Algebra


@[main]
private lemma main
  {s : Finset ι}
  {x : ι → ℝ}
-- given
  (h : ∀ i ∈ s, x i ≥ 0) :
-- imply
  ∑ i ∈ s, (x i) ≥ 0 := by
-- proof
  have := GeSumS.of.All_Ge (x := x) (y := fun _ => 0) h
  simp at this
  assumption


-- created on 2025-04-06
