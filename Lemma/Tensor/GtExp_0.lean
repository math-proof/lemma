import Lemma.Vector.GtExp_0
import Theorem.Data.Holor.Functions
open Vector


@[path]
private lemma main
  [ExpPos α]
-- given
  (x : Tensor α s) :
-- imply
  exp x > 0 :=
-- proof
  GtExp_0 x.data


-- created on 2026-07-27
