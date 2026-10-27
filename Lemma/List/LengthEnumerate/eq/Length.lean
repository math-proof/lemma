import Def.Data.List.List.Part5


@[path]
private lemma main
-- given
  (s : List α) :
-- imply
  s.enumerate.length = s.length := by
-- proof
  simp [List.enumerate]


-- created on 2025-06-02
