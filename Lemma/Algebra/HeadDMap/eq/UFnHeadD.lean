import Lemma.Basic


@[main]
private lemma main
  {s : List α}
  {f : α → β}
  {default : α} :
-- imply
  (s.map f).headD (f default) = f (s.headD default) := by
-- proof
  simp


-- created on 2024-07-01
