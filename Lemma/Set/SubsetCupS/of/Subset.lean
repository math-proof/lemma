import Lemma.Set.In_Cup.is.Any_In
open Set


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ⊆ B)
  (f : α → Set β) :
-- imply
  ⋃ x ∈ A, f x ⊆ ⋃ x ∈ B, f x := by
-- proof
  intro x hx
  let ⟨a, haA, h_In_fa⟩ := Any_In.of.In_Cup.double hx
  apply In_Cup.of.Any_In.double ⟨a, h haA, h_In_fa⟩


@[main]
private lemma fin.fn
  [DecidableEq α]
  {A B : Finset α}
-- given
  (h : A ⊆ B)
  (f : α → Finset β) :
-- imply
  ⋃ x ∈ A, f x ⊆ ⋃ x ∈ B, (f x : Set β) := by
-- proof
  intro x hx
  let ⟨a, haA, h_In_fa⟩ := Any_In.of.In_Cup.double hx
  apply In_Cup.of.Any_In.double ⟨a, h haA, h_In_fa⟩


@[main]
private lemma fin
  [DecidableEq α]
  {A B : Finset α}
-- given
  (h : A ⊆ B)
  (f : α → Set β) :
-- imply
  ⋃ x ∈ A, f x ⊆ ⋃ x ∈ B, f x := by
-- proof
  intro x hx
  let ⟨a, haA, h_In_fa⟩ := Any_In.of.In_Cup.double hx
  apply In_Cup.of.Any_In.double ⟨a, h haA, h_In_fa⟩


-- created on 2025-07-20
-- updated on 2025-07-29
