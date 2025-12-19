import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.StDiv_Add_Square.eq.One.of.StDiv.eq.One
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h : st (a / b) = 1) :
-- imply
  ¬((1 + 2 * a * b) / (1 + a² + b²)).Infinite := by
-- proof
  apply NotInfinite.of.NeSt_0
  linarith [StDiv_Add_Square.eq.One.of.StDiv.eq.One h]


-- created on 2025-12-16
-- updated on 2025-12-19
