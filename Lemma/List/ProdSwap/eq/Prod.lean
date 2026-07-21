import stdlib.List
import Lemma.Nat.NotLt.is.Ge
import Lemma.Nat.Lt.is.Le.Ne
import Lemma.Bool.Ne.is.NotEq
import Lemma.List.ProdAppend_Cons_Drop.eq.Prod.of.Lt.GtLength
open List Bool Nat


@[main]
private lemma main
  [CommMonoid α]
-- given
  (s : List α)
  (i j : ℕ) :
-- imply
  (s.swap i j).prod = s.prod := by
-- proof
  unfold List.swap
  split_ifs with h_eq h_lt? h_j h_i
  ·
    rfl
  ·
    apply ProdAppend_Cons_Drop.eq.Prod.of.Lt.GtLength h_j h_lt?
  ·
    rfl
  ·
    apply ProdAppend_Cons_Drop.eq.Prod.of.Lt.GtLength h_i
    apply Lt.of.Le.Ne
    ·
      apply Le.of.NotGt h_lt?
    ·
      symm
      apply Ne.of.NotEq h_eq
  ·
    rfl


-- created on 2025-06-14
