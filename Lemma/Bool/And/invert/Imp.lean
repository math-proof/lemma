import sympy.Basic


@[path]
private lemma main
  {p q : Prop} :
-- imply
  p ∧ q ↔ (q → p) ∧ q := by
-- proof
  constructor
  ·
    rintro ⟨hp, hq⟩
    exact ⟨fun _ => hp, hq⟩
  ·
    rintro ⟨h, hq⟩
    exact ⟨h hq, hq⟩


-- created on 2022-09-20
