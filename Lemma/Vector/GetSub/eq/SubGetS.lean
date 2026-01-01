import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Vector.GetNeg.eq.NegGet
import Lemma.Vector.GetAdd.eq.AddGetS
import sympy.vector.vector
open Int Vector


@[main, comm, fin, fin.comm]
private lemma main
  [SubNegMonoid α]
-- given
  (a b : List.Vector α n)
  (i : Fin n) :
-- imply
  (a - b)[i] = a[i] - b[i] := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [GetAdd.eq.AddGetS]
  rw [GetNeg.eq.NegGet]
  rw [Sub.eq.Add_Neg]


-- created on 2025-12-03
