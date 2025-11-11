import Lemma.Vector.FlattenMapRange.eq.Cast_UFn_0
import Lemma.Bool.SEq.is.EqCast.of.Eq
import sympy.vector.vector
open Vector Bool


@[main]
private lemma main
  {u : Fin 1 → List.Vector α n} :
-- imply
  ((List.Vector.range 1).map fun i => u i).flatten ≃ u 0 := by
-- proof
  apply SEq.of.Eq_Cast
  ·
    apply FlattenMapRange.eq.Cast_UFn_0
  ·
    simp


-- created on 2025-11-11
