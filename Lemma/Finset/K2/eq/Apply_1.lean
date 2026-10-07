import sympy.concrete.continuant
import sympy.Basic
open Continuant


@[main]
private lemma main
  [CommRing R]
-- given
  (x : ℕ → R) :
-- imply
  K x 2 = x 1 := by
-- proof
  simp [K]


-- created on 2026-10-07
