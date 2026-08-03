import Lemma.Real.DivPi9.lt.Div1'2
import Lemma.Nat.Lt.of.Lt.Lt
open Nat Real


@[main]
private lemma main:
-- imply
  sin (π / 9) < 1 / 2 := by
-- proof
  have h_Gt : π / 9 > 0 := by linarith [Real.pi_pos]
  have h_Lt : sin (π / 9) < π / 9 := Real.sin_lt h_Gt
  have := Lt.of.Lt.Lt h_Lt DivPi9.lt.Div1'2
  assumption


-- created on 2025-03-24
-- updated on 2025-04-04
