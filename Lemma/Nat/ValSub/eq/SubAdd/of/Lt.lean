import Lemma.Nat.Add
import Lemma.Nat.Add_Sub.eq.SubAdd.of.Gt
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.LtSub.is.Lt_Add.of.Ge
open Nat


@[main]
private lemma main
  {i j : Fin n}
-- given
  (h : i < j) :
-- imply
  (i - j).val = n + i.val - j.val := by
-- proof
  rw [Fin.sub_def]
  simp
  rw [Add.comm (a := n - ↑j)]
  rw [Add_Sub.eq.SubAdd.of.Gt j.isLt]
  rw [Add.comm (a := (i : ℕ))]
  rw [EqMod.of.Lt]
  apply LtSub.of.Lt_Add.Ge
  ·
    grind
  ·
    grind


-- created on 2026-09-01
