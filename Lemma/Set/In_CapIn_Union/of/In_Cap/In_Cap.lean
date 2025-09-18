import Lemma.Set.In_Cap.is.All_In
open Set


@[main]
private lemma main
  {f : α → Set α}
  {A B : Set α}
-- given
  (h₀ : x ∈ ⋂ x ∈ A, f x)
  (h₁ : x ∈ ⋂ x ∈ B, f x) :
-- imply
  x ∈ ⋂ x ∈ A ∪ B, f x := by
-- proof
  apply In_Cap.of.All_In.set
  intro a ha
  cases ha with
  | inl haA =>
    apply All_In.of.In_Cap.set h₀
    assumption
  | inr haB =>
    apply All_In.of.In_Cap.set h₁
    assumption


-- created on 2025-07-20
-- updated on 2025-08-02
