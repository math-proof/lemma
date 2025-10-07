import Lemma.Algebra.LeSumS.of.All_Le
open Algebra


@[main]
private lemma main
  {s : Finset ι}
  {x y : ι → ℝ}
-- given
  (h : ∀ i ∈ s, x i ≥ y i) :
-- imply
  ∑ i ∈ s, x i ≥ ∑ i ∈ s, y i :=
-- proof
  LeSumS.of.All_Le (x := y) (y := x) h


-- created on 2025-04-06
