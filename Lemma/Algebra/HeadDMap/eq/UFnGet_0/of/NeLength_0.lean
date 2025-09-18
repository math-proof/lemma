import Lemma.Basic


@[main]
private lemma main
  {s : List α}
  {default : β}
  {f : α → β}
-- given
  (h : s.length ≠ 0) :
-- imply
  (s.map f).headD default = f s[0] := by
-- proof
  match s with
  | .nil =>
    contradiction
  | .cons hd tl =>
    simp


-- created on 2024-07-01
