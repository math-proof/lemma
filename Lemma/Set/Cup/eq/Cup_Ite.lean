import sympy.Basic


@[main, comm]
private lemma main
  {A : Set α}
-- given
  (h : (x : α) → Decidable (x ∈ A))
  (f : α → Set β) :
-- imply
  ⋃ x ∈ A, f x = ⋃ x, if x ∈ A then
    f x
  else
    ∅ := by
-- proof
  ext x
  simp only [Set.iUnion_ite]
  constructor
  ·
    rintro ⟨a, haA, hxf⟩
    aesop
  ·
    rintro ⟨a, ⟨haA, hxf⟩⟩
    aesop
    aesop


-- created on 2025-08-04
-- updated on 2025-09-30
