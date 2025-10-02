import sympy.vector.vector
import Lemma.Algebra.ModMod.eq.Mod
open Algebra


@[main]
private lemma main
-- given
  (v : List α)
  (n : ℕ) :
-- imply
  v.rotate (n % v.length) = v.rotate n:= by
-- proof
  unfold List.rotate
  rw [ModMod.eq.Mod]


-- created on 2025-06-16
