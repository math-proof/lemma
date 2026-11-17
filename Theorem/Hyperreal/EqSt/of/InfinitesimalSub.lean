module

public import Theorem.Hyperreal.IsSt.is.Le0Mk.EqStdPart

public section

open Hyperreal ArchimedeanClass


public theorem Hyperreal.EqSt.of.InfinitesimalSub
  {x : ℝ*}
  {r : ℝ}
-- given
  (h : (x - r) → 0) :
-- imply
  stdPart x = r :=
-- proof
  (Le0Mk.EqStdPart.of.IsSt h).right


-- created on 2025-12-09
