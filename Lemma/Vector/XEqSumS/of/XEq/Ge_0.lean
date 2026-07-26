import sympy.sets.fancyset
import sympy.vector.vector
import Lemma.Hyperreal.XEqSumS.of.All_XEq.All_Ge_0
import Lemma.Vector.EqGet0_0
import Lemma.Vector.Sum.eq.Sum_Get
import Lemma.Vector.XEq.is.All_XEqGetS
open Hyperreal Vector


@[main]
private lemma main
  {a b : List.Vector ℝ* n}
-- given
  (h_pos : b ≥ 0)
  (h_xeq : a ≈ b) :
-- imply
  a.sum ≈ b.sum := by
-- proof
  rw [Sum.eq.Sum_Get, Sum.eq.Sum_Get (v := b)]
  apply Hyperreal.XEqSumS.of.All_XEq.All_Ge_0
  ·
    intro i
    refine ge_iff_le.mpr ?_
    convert h_pos i
    exact (EqGet0_0.fin (α := ℝ*) i).symm
  ·
    intro i
    exact All_XEqGetS.of.XEq h_xeq i


-- created on 2026-07-26
