import Def.Data.Holor.Det


@[path]
private lemma main
  [CommRing α]
  {A B : Tensor α s}
-- given
  (h : A = B) :
-- imply
  A.det = B.det := by
-- proof
  rw [h]


-- created on 2020-02-10
-- updated on 2026-10-26
