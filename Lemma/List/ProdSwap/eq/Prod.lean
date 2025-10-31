import stdlib.List
import Lemma.Nat.NotGt.is.Le
import Lemma.Nat.Lt.of.Le.Ne
import Lemma.Bool.Ne.is.NotEq
import Lemma.List.ProdAppend_Cons_Drop.eq.Prod.of.Lt.Lt_Length
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
    apply ProdAppend_Cons_Drop.eq.Prod.of.Lt.Lt_Length h_lt? h_j
  ·
    rfl
  ·
    have h_le := Le.of.NotGt h_lt?
    simp at h_eq
    have h_ne := Ne.of.NotEq h_eq
    have h_lt := Lt.of.Le.Ne h_ne.symm h_le
    apply ProdAppend_Cons_Drop.eq.Prod.of.Lt.Lt_Length h_lt h_i
  ·
    rfl


-- created on 2025-06-14
