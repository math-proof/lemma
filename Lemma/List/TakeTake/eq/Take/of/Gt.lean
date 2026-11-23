import Initialize.Tactic.Attr.Basic
import Theorem.List.TakeTake.eq.Take.of.Ge
open List


/--
| attributes | lemma |
| :---: | :---: |
| path | List.TakeTake.eq.Take.of.Gt |
| comm | List.Take.eq.TakeTake.of.Gt |
-/
@[path, comm]
private lemma main
-- given
  (h : i > j)
  (s : List α) :
-- imply
  (s.take i).take j = s.take j := by
-- proof
  apply TakeTake.eq.Take.of.Ge (le_of_lt h)


-- created on 2025-10-27
-- updated on 2026-11-22
