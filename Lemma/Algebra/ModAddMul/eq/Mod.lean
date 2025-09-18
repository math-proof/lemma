import Lemma.Algebra.Add
import Lemma.Algebra.ModAdd_Mul.eq.Mod
open Algebra


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (a b c : Z) :
-- imply
  (b * c + a) % c = a % c := by
-- proof
  rw [Add.comm]
  apply ModAdd_Mul.eq.Mod


@[main]
private lemma left
  [IntegerRing Z]
-- given
  (a b c : Z) :
-- imply
  (b * c + a) % b = a % b := by
-- proof
  rw [Add.comm]
  apply ModAdd_Mul.eq.Mod.left


-- created on 2025-07-08
