import Def.Data.List.List.Part5


@[path, comm]
private lemma main
-- given
  (s : List α) :
-- imply
  s.array_slice i d = (s.drop i).take d := by
-- proof
  simp [List.array_slice]


-- created on 2025-05-08
