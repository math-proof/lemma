module

public import Theorem.List.Permute.eq.Ite
public import Theorem.List.Slice.eq.Nil
public import Initialize.Tactic.Attr.Basic

public section

open List


@[comm]
public theorem List.EqPermute
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  s.permute i 0 = s := by
-- proof
  rw [Permute.eq.Ite]
  simp
  rw [Slice.eq.Nil]
  simp


-- created on 2025-06-16
