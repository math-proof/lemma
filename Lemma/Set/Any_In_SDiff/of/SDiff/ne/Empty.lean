import Lemma.Set.Any_In.is.Ne_Empty
import Lemma.Set.In.of.In_SDiff
open Set


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A \ B ≠ ∅) :
-- imply
  ∃ i ∈ A, i ∈ A \ B := by
-- proof
  obtain ⟨i, hi⟩ := Any_In.of.Ne_Empty h
  exact ⟨i, In.of.In_SDiff hi, hi⟩


-- created on 2018-03-24
