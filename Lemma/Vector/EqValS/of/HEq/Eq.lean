import sympy.vector.vector
import Lemma.Vector.HEq.is.HEqValS.of.Eq
import Lemma.List.Eq.of.HEq
open Vector List


@[main]
private lemma main
  {a : List.Vector α n}
  {b : List.Vector α m}
-- given
  (h₀ : n = m)
  (h₁ : HEq a b) :
-- imply
  a.val = b.val := by
-- proof
  have := HEqValS.of.HEq.Eq h₀ h₁
  apply Eq.of.HEq this


-- created on 2025-05-21
-- updated on 2025-08-02
