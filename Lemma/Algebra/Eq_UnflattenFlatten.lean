import stdlib.List.Vector
import Lemma.Algebra.Eq_FlattenUnflatten
import Lemma.Algebra.Eq.of.EqFlattenS
open Algebra


@[main]
private lemma main
  [Inhabited α]
-- given
  (v : List.Vector (List.Vector α n) m) :
-- imply
  v = v.flatten.unflatten := by
-- proof
  have := Eq_FlattenUnflatten v.flatten
  apply Eq.of.EqFlattenS this


-- created on 2025-05-11
