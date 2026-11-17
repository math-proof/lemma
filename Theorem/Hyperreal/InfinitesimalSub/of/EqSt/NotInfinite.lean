module

public import Theorem.Hyperreal.IsSt.is.Le0Mk.EqStdPart

public section

open Hyperreal ArchimedeanClass


public theorem Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
  {x : ℝ*}
  {r : ℝ}
-- given
  (h_x : ¬x → ∞)
  (h_st : stdPart x = r) :
-- imply
  (x - r) → 0 :=
  IsSt.of.Le0Mk.EqStdPart (not_lt.mp h_x) h_st


-- created on 2025-12-09
