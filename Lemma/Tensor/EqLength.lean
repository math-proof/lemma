import Def.Data.Holor.Defs.Part4


@[path, grind =]
private lemma main
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.length = n := by
-- proof
  simp [Tensor.length]


-- created on 2025-12-08
