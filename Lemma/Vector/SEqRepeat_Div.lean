import Lemma.Bool.SEq.is.Eq
import Lemma.Nat.Div.eq.One.of.Ne_0
import Lemma.Vector.SEqRepeat_1
import sympy.vector.Basic
open Bool Nat Vector


@[main]
private lemma main
-- given
  (v : List.Vector α n) :
-- imply
  v.repeat (n / n) ≃ v := by
-- proof
  if h : n = 0 then
    subst h
    simp
    apply SEq.of.Eq
    ext i
    have h_i := i.isLt
    simp at h_i
  else
    rw [Div.eq.One.of.Ne_0 h]
    apply SEqRepeat_1


-- created on 2026-07-10
