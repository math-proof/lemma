import Def.Data.Tensor.Defs


@[path, grind =]
private lemma main
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.length = n := by
-- proof
  simp [Tensor.length]


-- created on 2025-12-08
-- updated on 2026-11-20
