import Lemma.Vector.GetMap.eq.FunGet
import Lemma.Algebra.EqGetRange
open Algebra Vector


@[main]
private lemma fin
-- given
  (i : Fin n) :
-- imply
  ((List.Vector.range n).map f).get i = f i := by
-- proof
  congr
  simp [EqGetRange.fin]


@[main]
private lemma main
-- given
  (i : Fin n) :
-- imply
  ((List.Vector.range n).map f)[i] = f i :=
-- proof
  fin i


-- created on 2025-06-29
