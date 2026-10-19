import stdlib.List


@[path]
private lemma main
-- given
  (s : List α) :
-- imply
  s.enumerate.length = s.length := by
-- proof
  simp [List.enumerate]


-- created on 2025-06-02
