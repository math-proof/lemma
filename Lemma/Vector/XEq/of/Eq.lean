import Lemma.Hyperreal.XEq.of.Eq
import Lemma.Vector.XEq.is.All_XEqGetS
import sympy.vector.vector


@[main]
private lemma main
  [XEq α]
  {a b : List.Vector α n}
-- given
  (h : a = b) :
-- imply
  a ≈ b := by
-- proof
  subst h
  apply Vector.XEq.of.All_XEqGetS
  intro i
  exact Hyperreal.XEq.of.Eq rfl


-- created on 2026-07-29
