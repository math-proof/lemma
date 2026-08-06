import Lemma.Nat.Le.of.Lt
import Lemma.Real.SubArcsinS.eq.DivPi2.of.Le_0
open Nat Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x < 0) :
-- imply
  arcsin (√(1 - x²)) - arcsin x = π / 2 :=
-- proof
  SubArcsinS.eq.DivPi2.of.Le_0 (Le.of.Lt h)


-- created on 2018-07-13
-- updated on 2025-04-10
