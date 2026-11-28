module

public import Initialize.Tactic.Attr.Basic

public import Theorem.List.Drop.eq.ListGet.of.GeLength_1
public import Theorem.List.Cons.is.Eq.Eq

public section

open List


@[comm]
public theorem List.Drop.eq.ListGetS.of.GeLength_2
  {s : List α}
-- given
  (h : s.length ≥ 2) :
-- imply
  s.drop (s.length - 2) = [s[s.length - 2], s[s.length - 1]] := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1.of.GtLength (by omega)]
  apply (List.cons.injEq _ _ _ _).mpr
  constructor
  ·
    rfl
  ·
    simp [show s.length - 2 + 1 = s.length - 1 by omega]
    apply Drop.eq.ListGet.of.GeLength_1
    omega


public theorem List.ListGetS.eq.Drop.of.GeLength_2
  {s : List α}
  (h : s.length ≥ 2) :
  [s[s.length - 2], s[s.length - 1]] = s.drop (s.length - 2) :=
  (List.Drop.eq.ListGetS.of.GeLength_2 h).symm


-- created on 2026-01-03
