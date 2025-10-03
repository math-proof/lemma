import sympy.vector.vector
import Lemma.Algebra.IsConstantMap.of.IsConstant
open Algebra


@[main]
private lemma main
  {s : List.Vector α n}
-- given
  (h : s is constant)
  (f : α → β) :
-- imply
  (s.map f) is constant :=
-- proof
  IsConstantMap.of.IsConstant h f


-- created on 2025-10-03
