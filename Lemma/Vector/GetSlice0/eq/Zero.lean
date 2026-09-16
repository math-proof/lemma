import sympy.vector.Basic
import Lemma.Vector.EqGet0_0
import Lemma.Vector.Zero.eq.Replicate
import Lemma.List.LengthRange.eq.Length
open Vector


@[main]
private lemma main
  [Zero α]
-- given
  (n : ℕ) (s : Slice) :
-- imply
  (0 : List.Vector α n).getSlice s = 0 := by
-- proof
  simp [List.Vector.getSlice, EqGet0_0.val, List.Vector.indices,
    List.Vector.map, List.map_const', List.LengthRange.eq.Length]
  apply Subtype.ext
  simp [Zero.eq.Replicate, List.Vector.replicate, Subtype.coe_mk]


-- created on 2026-09-16
