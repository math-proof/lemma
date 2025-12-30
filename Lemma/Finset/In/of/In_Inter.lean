import Lemma.Finset.SubsetInter
import Lemma.Set.In.of.In.Subset
open Finset Set


@[main]
private lemma main
  [DecidableEq α]
  {x : α}
  {A B : Finset α}
-- given
  (h : x ∈ A ∩ B) :
-- imply
  x ∈ B := by
-- proof
  apply In.of.In.Subset _ h
  apply SubsetInter


@[main]
private lemma left
  [DecidableEq α]
  {x : α}
  {A B : Finset α}
-- given
  (h : x ∈ A ∩ B) :
-- imply
  x ∈ A := by
-- proof
  apply In.of.In.Subset _ h
  apply SubsetInter.left


-- created on 2025-12-30
