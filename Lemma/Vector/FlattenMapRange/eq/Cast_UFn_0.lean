import Lemma.Bool.EqCast.of.SEq
import Lemma.Vector.FlattenMapRange.as.UFn_0
open Vector Bool


@[main]
private lemma main
  (u : Fin 1 → List.Vector α n) :
-- imply
  ((List.Vector.range 1).map fun i => u i).flatten = cast (by simp) (u 0) :=
-- proof
  Eq_Cast.of.SEq (FlattenMapRange.as.UFn_0 u)


-- created on 2025-11-11
-- updated on 2026-06-14
