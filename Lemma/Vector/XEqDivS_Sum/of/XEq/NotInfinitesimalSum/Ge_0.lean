import Lemma.Hyperreal.Infinitesimal.is.Infinitesimal.of.XEq
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.XEq.is.OrAndS
import Lemma.Hyperreal.XEqDivS.of.XEq.XEq.NotInfinitesimal
import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Vector.XEq.is.All_XEqGetS
import Lemma.Vector.XEqSumS.of.XEq.Ge_0
open Hyperreal Vector


@[main]
private lemma main
  {a b : List.Vector ℝ* n}
-- given
  (h_pos : b ≥ 0)
  (h_not_sum : ¬(b.sum → 0))
  (h : a ≈ b) :
-- imply
  a / a.sum ≈ b / b.sum := by
-- proof
  have h_sum := XEqSumS.of.XEq.Ge_0 h_pos h
  have h_not_sum_a := NotInfinitesimal.of.NotInfinitesimal.XEq h_sum h_not_sum
  refine Vector.XEq.of.All_XEqGetS.fin ?_
  intro i
  simp [GetDiv.eq.DivGet.fin]
  if hi : a.get i → 0 then
    have hi' := Infinitesimal.of.Infinitesimal.XEq (All_XEqGetS.of.XEq h i) hi
    apply XEq.of.OrAndS
    left
    constructor
    .
      apply InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal hi h_not_sum_a
    .
      apply InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal hi' h_not_sum
  else
    apply XEqDivS.of.XEq.XEq.NotInfinitesimal h_not_sum (All_XEqGetS.of.XEq h i) h_sum


-- created on 2026-07-26
