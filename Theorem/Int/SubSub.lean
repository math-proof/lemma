module

public import Mathlib
public import Theorem.Int.Sub_Add.eq.SubSub

public section

open Int


public theorem Int.SubSub.Comm
  [SubtractionCommMonoid α]
  {a b c : α} :
-- imply
  a - b - c = a - c - b := by
-- proof
  repeat rw [SubSub.eq.Sub_Add]
  rw [add_comm]


-- created on 2025-06-06
-- updated on 2025-10-12
