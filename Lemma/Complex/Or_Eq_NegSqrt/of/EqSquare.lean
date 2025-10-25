import Lemma.Algebra.EqSquareSqrt
import Lemma.Real.OrEqS.of.EqSquareS
open Algebra Real


@[main]
private lemma main
  {x c : ℂ}
-- given
  (h : x² = c) :
-- imply
  x = √c ∨ x = -√c := by
-- proof
  let t := √c
  have h_t : t² = c := EqSquareSqrt
  exact OrEqS.of.EqSquareS (h_t.symm ▸ h)


-- created on 2024-07-01
