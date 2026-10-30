import Lemma.Nat.Add
import Def.Data.List.List.Basic
open Nat


@[path]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ i)
  (a : α) :
-- imply
  (s.insertIdx i a).length = s.length + 1:=
-- proof
  List.length_insertIdx_of_le_length h a


-- created on 2026-07-12
