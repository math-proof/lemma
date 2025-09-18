import Lemma.Algebra.EqArraySliceS.of.Eq.Eq.Eq
open Algebra


@[main]
private lemma main
  {v : List.Vector α n}
  {v' : List.Vector α n'}
-- given
  (h : v ≃ v')
  (i s : ℕ) :
-- imply
  v.array_slice i s ≃ v'.array_slice i s := by
-- proof
  apply EqArraySliceS.of.Eq.Eq.Eq rfl rfl h


-- created on 2025-06-29
