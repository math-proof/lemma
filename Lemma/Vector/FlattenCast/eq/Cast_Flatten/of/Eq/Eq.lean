import stdlib.SEq
import sympy.vector.vector
import Lemma.Bool.EqCast.of.SEq
import Lemma.Vector.FlattenCast.as.Flatten.of.Eq.Eq
import Lemma.Nat.EqMulS.of.Eq.Eq
open Bool Vector Nat


@[main, comm 3]
private lemma main
-- given
  (h_m : m = m')
  (h_n : n = n')
  (v : List.Vector (List.Vector α n) m) :
-- imply
  (cast (congrArg₂ (fun n m => List.Vector (List.Vector α n) m) h_n h_m) v).flatten = cast (congrArg (List.Vector α) (EqMulS.of.Eq.Eq h_m h_n)) v.flatten := by
-- proof
  apply Eq_Cast.of.SEq
  apply FlattenCast.as.Flatten.of.Eq.Eq h_m h_n


-- created on 2025-10-17
