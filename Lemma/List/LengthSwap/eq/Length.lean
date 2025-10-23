import Lemma.List.LengthAppend_Cons_Drop.eq.Length.of.Lt.Lt_Length
import Lemma.Nat.NotGt.is.Le
import Lemma.Nat.Lt.of.Le.Ne
import Lemma.Bool.Ne.is.NotEq
open List Bool Nat


@[main]
private lemma main
-- given
  (a : List α)
  (i j : ℕ) :
-- imply
  (a.swap i j).length = a.length := by
-- proof
  unfold List.swap
  split_ifs with h_eq h_lt? h_j h_i
  ·
    rfl
  ·
    apply LengthAppend_Cons_Drop.eq.Length.of.Lt.Lt_Length h_lt? h_j
  ·
    rfl
  ·
    have h_le := Le.of.NotGt h_lt?
    simp at h_eq
    have h_ne := Ne.of.NotEq h_eq
    have h_lt := Lt.of.Le.Ne h_ne.symm h_le
    apply LengthAppend_Cons_Drop.eq.Length.of.Lt.Lt_Length h_lt h_i
  ·
    rfl


-- created on 2025-05-12
-- updated on 2025-05-15
