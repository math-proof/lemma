import Lemma.Nat.Le.of.Lt_Add_1
import Lemma.Nat.Gt.of.Ge.Gt
import Lemma.Nat.LtSub_1.of.Le.Gt_0
open Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h₀ : i > 0)
  (h₁ : s.length > i) :
-- imply
  s.tail.length > i - 1 := by
-- proof
  match s with
  | .nil =>
    simp
    contradiction
  | head :: tail =>
    simp_all
    have h_Le := Le.of.Lt_Add_1 h₁
    have := Gt.of.Ge.Gt h_Le h₀
    apply LtSub_1.of.Le.Gt_0 this h_Le


-- created on 2025-05-05
