import Lemma.Bool.Bool.eq.Ite
import sympy.Basic
open Bool


@[main]
private lemma main
  [Decidable p]
-- given
  (h : p) :
-- imply
  Bool.toNat p = 1 := by
-- proof
  rw [Bool.eq.Ite]
  simp [h]


-- created on 2026-10-03
