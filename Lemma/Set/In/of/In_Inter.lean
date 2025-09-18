import Lemma.Set.In.of.In.Subset
import Lemma.Set.SubsetInter
open Set


@[main]
private lemma left
  {x : α}
  {A B : Set α}
-- given
  (h : x ∈ A ∩ B) :
-- imply
  x ∈ A := by
-- proof
  apply In.of.In.Subset _ h
  apply SubsetInter.left


@[main]
private lemma main
  {x : α}
  {A B : Set α}
-- given
  (h : x ∈ A ∩ B) :
-- imply
  x ∈ B := by
-- proof
  apply In.of.In.Subset _ h
  apply SubsetInter


@[main]
private lemma fin
  [DecidableEq α]
  {x : α}
  {A B : Finset α}
-- given
  (h : x ∈ A ∩ B) :
-- imply
  x ∈ B := by
-- proof
  apply In.of.In.Subset _ h
  apply SubsetInter.fin


@[main]
private lemma left.fin
  [DecidableEq α]
  {x : α}
  {A B : Finset α}
-- given
  (h : x ∈ A ∩ B) :
-- imply
  x ∈ A := by
-- proof
  apply In.of.In.Subset _ h
  apply SubsetInter.left.fin


-- created on 2025-07-19
