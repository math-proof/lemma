import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {s : List α}
-- given
  (h : s.length ≠ 0)
  (default : α):
-- imply
  s.headD default = s[0] := by
-- proof
  match s with
  | .nil =>
    contradiction
  | .cons hd tl =>
    simp


-- created on 2024-07-01
-- updated on 2026-10-26
