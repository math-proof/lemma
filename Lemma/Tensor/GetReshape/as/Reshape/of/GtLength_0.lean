import Lemma.Tensor.GetReshape.as.Reshape.of.Prod.GtLength_0
import Def.Data.Holor.Reshape
import Def.Data.Holor.Prod
open Tensor


@[path, fin, cast, cast.fin]
private lemma main
  {s s' : List ℕ}
-- given
  (h : s'.length > 0)
  (X : Tensor α s)
  (i : Fin s'[0]) :
-- imply
  (X.reshape (s' ++ s) (by simp))[i]'(by rw [Length.eq.Get_0.of.GtLength_0 (by grind)]; grind) ≃ X.reshape (s'.tail ++ s) (by simp) := by
-- proof
  apply GetReshape.as.Reshape.of.Prod.GtLength_0 h (by grind) X (s' := s)


-- created on 2026-01-12
-- updated on 2026-10-26
