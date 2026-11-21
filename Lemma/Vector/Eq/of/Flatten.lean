import Def.Data.Vector.Basic
import Lemma.Vector.Eq.of.FlattenMap.Length
open Vector


@[path]
private lemma main
  {a b : List.Vector (List.Vector α n) m}
-- given
  (h : a.flatten = b.flatten) :
-- imply
  a = b := by
-- proof
  apply Subtype.ext
  apply Eq.of.FlattenMap.Length (by simp)
  apply congrArg Subtype.val h


-- created on 2025-05-11
-- updated on 2026-11-20
