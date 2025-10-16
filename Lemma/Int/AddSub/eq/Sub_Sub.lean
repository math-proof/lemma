import Lemma.Nat.Eq.of.Le.Ge
import Lemma.Nat.EqAddSub.of.Gt
import Lemma.Nat.EqSubAdd
import Lemma.Int.Sub_Add.eq.SubSub


@[main, comm]
private lemma main
  [SubtractionCommMonoid α]
-- given
  (a b c : α) :
-- imply
  a - b + c = a - (b - c) :=
-- proof
  sub_add a b c


-- created on 2025-03-24
-- updated on 2025-06-18
