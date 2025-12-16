import sympy.core.power
import Lemma.Nat.EqDivS.of.Eq
import Lemma.Rat.DivAdd.eq.Add1Div.of.Ne_0
open Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h : a * b > 0) :
-- imply
  (1 + a² + b²) / (1 + 2 * a * b) = 1 + (a - b)² / (1 + 2 * a * b) := by
-- proof
  rw [Add1Div.eq.DivAdd.of.Ne_0]
  ·
    apply EqDivS.of.Eq
    ring
  ·
    nlinarith


-- created on 2025-12-11
