import sympy.vector.vector
import Lemma.Vector.EqGetRange
open Vector


@[main]
private lemma main
  [HPow α β α]
-- given
  (f : Fin n → α)
  (g : Fin n → β) :
-- imply
  ((List.Vector.range n).map f) ^ ((List.Vector.range n).map g) = (List.Vector.range n).map (fun i => f i ^ g i) := by
-- proof
  ext i
  simp [HPow.hPow, EqGetRange.fin]


-- created on 2026-08-23
