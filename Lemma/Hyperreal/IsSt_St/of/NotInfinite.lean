import Lemma.Hyperreal.IsSt.is.Le0Mk.EqStdPart
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : ¬x → ∞) :
-- imply
  (x - stdPart x) → 0 :=
  IsSt.of.Le0Mk.EqStdPart (not_lt.mp h) rfl


-- created on 2025-12-27
