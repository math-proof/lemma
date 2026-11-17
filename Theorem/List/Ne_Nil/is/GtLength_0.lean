module

public import Theorem.Nat.Ne.of.Gt
public import Theorem.List.Ne_Nil.of.NeLength_0

public section

open List Nat


@[comm, mp, mpr]
public theorem List.Ne_Nil.is.GtLength_0
-- given
  (s : List α) :
-- imply
  s ≠ [] ↔ s.length > 0 := by
-- proof
  constructor <;>
    intro h
  .
    by_contra h
    simp at h
    contradiction
  ·
    have h := Ne.of.Gt h
    apply Ne_Nil.of.NeLength_0 h


-- created on 2025-05-08
