import Lemma.Nat.EqSub.of.EqAdd
import Lemma.Nat.EqSubAdd
import Lemma.Nat.EqAddS.is.Eq
open Nat


@[main, comm, mp, mpr, mp.comm, mpr.comm]
private lemma left
  [AddCommGroup α]
-- given
  (d x y : α) :
-- imply
  y - d = x ↔ y = d + x := by
-- proof
  aesop


@[main, comm, mp, mpr, mp.comm, mpr.comm]
private lemma main
  [AddGroup α]
-- given
  (d x y : α) :
-- imply
  y - x = d ↔ y = d + x := by
-- proof
  aesop

-- created on 2025-04-26
