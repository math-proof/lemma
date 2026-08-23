import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Any_Or.is.OrAnyS |
| comm | Bool.OrAnyS.is.Any_Or |
| mp | Bool.OrAnyS.of.Any_Or |
| mpr | Bool.Any_Or.of.OrAnyS |
-/
@[main, comm, mp, mpr]
private lemma main
  {p q : α → Prop} :
-- imply
  (∃ x : α, p x ∨ q x) ↔ (∃ x : α, p x) ∨ (∃ x : α, q x) := by
-- proof
  grind


@[main, comm, mp, mpr]
private lemma set
  {p q : α → Prop}
  {s : Set α}:
-- imply
  (∃ x ∈ s, p x ∨ q x) ↔ (∃ x ∈ s, p x) ∨ (∃ x ∈ s, q x) := by
-- proof
  aesop

-- created on 2019-02-28
-- updated on 2025-07-30
