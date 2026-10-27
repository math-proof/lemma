import Def.Data.Holor.Defs.Part4
import Def.Data.Holor.Repeat


@[path]
private lemma main
  {A B : Tensor α s}
-- given
  (h : A = B)
  (n : ℕ)
  (d : Fin s.length) :
-- imply
  A.repeat d n = B.repeat d n := by
-- proof
  subst h
  simp


-- created on 2026-01-10
