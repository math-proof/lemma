module

public import Theorem.List.Swap.eq.Ite
public import Theorem.Bool.Ne.is.NotEq
public import Theorem.List.ProdAppend_Cons_Drop.eq.Prod.of.Lt.GtLength
public import Theorem.Nat.NotLt.is.Ge

public section

open List Bool Nat


public theorem List.ProdSwap.eq.Prod
  [CommMonoid α]
-- given
  (s : List α)
  (i j : ℕ) :
-- imply
  (s.swap i j).prod = s.prod := by
-- proof
  rw [Swap.eq.Ite]
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
-- updated on 2026-08-24
