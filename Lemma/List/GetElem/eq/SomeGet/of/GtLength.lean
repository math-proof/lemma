import Initialize.Tactic.Attr.Basic
import Def.Data.List.List.Basic


@[path]
private lemma main
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  s[i]? = some s[i] := by
-- proof
  simp [h]


-- created on 2025-05-15
-- updated on 2026-11-18
