import Lemma.Vector.GetSub.eq.SubGetS
import sympy.vector.vector
open Vector


@[main]
private lemma main
  [SubNegMonoid α]
-- given
  (x : List.Vector α n)
  (a : α) :
-- imply
  x - a = x - List.Vector.replicate n a := by
-- proof
  conv_lhs => simp [HSub.hSub]
  ext i
  rw [GetSub.eq.SubGetS.fin]
  simp [HSub.hSub]


-- created on 2025-12-03
