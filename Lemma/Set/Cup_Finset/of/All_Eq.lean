import Lemma.Set.Cup.of.All_Eq
open Set


@[main]
private lemma main
  {ι : Sort u}
  {x y : ι → α}
-- given
  (h : ∀ i : ι, x i = y i) :
-- imply
  ⋃ i : ι, ({x i} : Set α) = ⋃ i : ι, ({y i} : Set α) := by
-- proof
  apply Cup.of.All_Eq
  intro i
  rw [h i]


@[main]
private lemma set
  {S : Set ι}
  {x y : ι → α}
-- given
  (h : ∀ i ∈ S, x i = y i) :
-- imply
  ⋃ i ∈ S, ({x i} : Set α) = ⋃ i ∈ S, ({y i} : Set α) := by
-- proof
  apply Cup.of.All_Eq.set
  intro i hi
  rw [h i hi]


-- created on 2020-07-23
-- updated on 2026-09-07
