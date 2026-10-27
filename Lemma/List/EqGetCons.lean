import Def.Data.List.List.Part5


@[path, fin]
private lemma main
-- given
  (head : α)
  (tail : List α) :
-- imply
  (head :: tail)[0] = head := by
-- proof
  simp


-- created on 2025-11-07
