import Lemma.Algebra.EqMin_SubMulS
import Lemma.Algebra.GetUnflatten.as.ArraySlice
import Lemma.Logic.EqCast.of.SEq
open Algebra Logic


@[main]
private lemma main
-- given
  (v : List.Vector α (m * n))
  (i : Fin m) :
-- imply
  v.unflatten[i] = cast (by rw [EqMin_SubMulS m n i]) (v.array_slice (i * n) n) := by
-- proof
  apply Eq_Cast.of.SEq
  apply GetUnflatten.as.ArraySlice


-- created on 2025-07-15
