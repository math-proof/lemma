import Lemma.Set.In_Cup.is.Any_In
open Set


@[main]
private lemma main
  {ι : Sort v}
  {A : ι → Set α}
  {x : α}
-- given
  (h : ∀ i : ι, x ∉ A i) :
-- imply
  x ∉ ⋃ i : ι, A i := by
-- proof
  rw [In_Cup.is.Any_In]
  rintro ⟨i, hi⟩
  simp_all


-- created on 2025-07-29
