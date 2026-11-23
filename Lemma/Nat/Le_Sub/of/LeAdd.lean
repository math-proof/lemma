import Initialize.Tactic.Attr.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.Le_Sub.of.LeAdd |
| comm 1 | Nat.GeSub.of.Ge_Add |
-/
@[path, comm 1]
private lemma main
  {a b c : ℕ}
-- given
  (h : a + b ≤ c) :
-- imply
  a ≤ c - b :=
-- proof
  Nat.le_sub_of_add_le h

@[path, comm 1]
private lemma left
  {a b c : ℕ}
-- given
  (h : a + b ≤ c) :
-- imply
  b ≤ c - a :=
-- proof
  Nat.le_sub_of_add_le' h


-- created on 2025-08-02
-- updated on 2026-11-23
