import Lemma.Set.In_Cap.is.All_In
open Set


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ⊇ B)
  (f : α → Set α) :
-- imply
  ⋂ x ∈ A, f x ⊆ ⋂ x ∈ B, f x := by
-- proof
  intro x hx
  apply In_Cap.of.All_In.set
  intro b hb
  apply All_In.of.In_Cap.set hx
  apply h hb


-- created on 2025-07-20
-- updated on 2025-08-02
