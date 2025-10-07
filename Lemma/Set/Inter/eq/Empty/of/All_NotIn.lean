import Lemma.Bool.Or_Not.of.All
import Lemma.Set.Any_In.is.Ne_Empty
open Set Bool


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : ∀ x ∈ A, x ∉ B) :
-- imply
  A ∩ B = ∅ := by
-- proof
  have := Or_Not.of.All h
  contrapose this
  have := Any_In.of.Ne_Empty this
  aesop


-- created on 2025-07-29
