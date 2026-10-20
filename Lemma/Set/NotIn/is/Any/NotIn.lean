import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Set.NotIn.is.Any.NotIn |
| mp | Set.Any.NotIn.of.NotIn |
| mpr | Set.NotIn.of.Any.NotIn |
-/
@[path, mp, mpr]
private lemma main
  {n : ℕ}
  {x : Fin n → α}
  {S : Set α} :
-- imply
  (¬ ∀ i, x i ∈ S) ↔ ∃ i, x i ∉ S :=
-- proof
  not_forall


-- created on 2023-07-02
-- updated on 2026-10-17
