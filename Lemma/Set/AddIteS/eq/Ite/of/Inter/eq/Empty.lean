import sympy.Basic


@[main]
private lemma main
  [Add α]
  {A B : Set β}
  {x : β}
  {a a' b b' : α}
  [Decidable (x ∈ A)]
  [Decidable (x ∈ B)]
-- given
  (h : A ∩ B = ∅) :
-- imply
  (if x ∈ A then
    a
  else
    a') + (if x ∈ B then
    b
  else
    b') =
    if x ∈ A then
      a + b'
    else if x ∈ B then
      a' + b
    else
      a' + b' := by
-- proof
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> simp [hA, hB]
  have : x ∈ A ∩ B := ⟨hA, hB⟩
  simp [h] at this


-- created on 2020-07-04
-- updated on 2026-09-07
