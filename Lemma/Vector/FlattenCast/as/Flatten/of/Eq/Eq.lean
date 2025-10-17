import stdlib.SEq
import sympy.vector.vector
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Vector


@[main, comm 3]
private lemma main
-- given
  (h_m : m = m')
  (h_n : n = n')
  (v : List.Vector (List.Vector α n) m) :
-- imply
  (cast (congrArg₂ (fun n m => List.Vector (List.Vector α n) m) h_n h_m) v).flatten ≃ v.flatten := by
-- proof
  subst h_m h_n
  aesop


-- created on 2025-10-17
