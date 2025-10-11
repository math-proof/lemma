import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Vector.GetUnflatten.as.ArraySlice
import Lemma.Vector.SEqArraySliceS.of.SEq.Eq.Eq
open Vector Bool


@[main]
private lemma main
  {v : List.Vector α N}
  {v' : List.Vector α (m * n)}
-- given
  (h : v' ≃ v)
  (i : Fin m) :
-- imply
  v'.unflatten[i] ≃ v.array_slice (i * n) n := by
-- proof
  apply SEq.of.SEq.SEq (c := v'.array_slice (i * n) n)
  ·
    apply GetUnflatten.as.ArraySlice
  ·
    apply SEqArraySliceS.of.SEq.Eq.Eq rfl rfl h.symm


-- created on 2025-05-31
