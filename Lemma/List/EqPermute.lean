import Initialize.Tactic.Attr.Basic
import Lemma.List.Permute.eq.Ite
import Lemma.List.Slice.eq.Nil
open List


/--
| attributes | lemma |
| :---: | :---: |
| path | List.EqPermute |
| comm | List.Eq_Permute |
-/
@[path, comm]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  s.permute i 0 = s := by
-- proof
  rw [Permute.eq.Ite]
  simp
  rw [Slice.eq.Nil]
  simp


-- created on 2025-06-16
-- updated on 2026-11-22
