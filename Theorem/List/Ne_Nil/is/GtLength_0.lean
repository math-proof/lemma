module

public import Initialize.Tactic.Attr.Basic

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

/-- Explicit alias of the `mp` direction of `List.Ne_Nil.is.GtLength_0`,
so the name is visible across modules (`@[comm]` does not export it). -/
public theorem List.GtLength_0.of.Ne_Nil
-- given
  {s : List α}
  (h : s ≠ []) :
-- imply
  s.length > 0 :=
  (List.Ne_Nil.is.GtLength_0 s).mp h


-- created on 2025-05-08
