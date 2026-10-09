import Lemma.Bool.EqCast.of.SEq
import Lemma.Finset.Any_In.is.Ne_Empty
import Lemma.Finset.Eq.of.All_SEq.Ne_Empty
open Bool Finset


@[path]
private lemma main
  {Vector : α → Sort v}
  {s : Finset ι}
  {x : ι → Vector n}
  {y : ι → Vector n'}
-- given
  (h_s : s ≠ ∅)
  (h : ∀ i ∈ s, x i ≃ y i) :
-- imply
  ∀ i ∈ s, cast (congrArg Vector (Eq.of.All_SEq.Ne_Empty h_s h)) (x i) = y i := by
-- proof
  intro i hi
  apply EqCast.of.SEq
  exact h i hi


-- created on 2025-11-06
