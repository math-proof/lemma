import Lemma.Algebra.EqAddSub.of.Ge
import Lemma.Algebra.Sub.eq.Add_Neg
import Lemma.Algebra.LeAddS.is.Le
open Algebra


@[main, comm, mp, mpr]
private lemma main
  [OrderedAddCommGroup α]
-- given
  (x y z : α) :
-- imply
  x - z ≤ y - z ↔ x ≤ y := by
-- proof
  constructor <;>
    intro h
  ·
    rw [Sub.eq.Add_Neg (a := x), Sub.eq.Add_Neg (a := y)] at h
    apply Le.of.LeAddS h
  ·
    rw [Sub.eq.Add_Neg (a := x), Sub.eq.Add_Neg (a := y)]
    apply LeAddS.of.Le _ h


-- created on 2025-05-14
