import Lemma.Hyperreal.Infinitesimal.is.XEq_0
import Lemma.Hyperreal.XEqExpS.of.InfinitesimalSub
import Lemma.Vector.GetSub.eq.SubGetS
import Lemma.Vector.XEq.is.All_XEqGetS
open Hyperreal Vector


@[main]
private lemma main
  {a b : List.Vector ℝ* n}
-- given
  (h : a - b ≈ 0) :
-- imply
  exp a ≈ exp b := by
-- proof
  simp [Exp.exp]
  apply XEq.of.All_XEqGetS.fin
  intro i
  simp
  apply XEqExpS.of.InfinitesimalSub
  apply Infinitesimal.of.XEq_0
  rw [SubGetS.eq.GetSub.fin]
  have h := All_XEqGetS.of.XEq.fin h i
  rwa [EqGet0_0.fin] at h


-- created on 2025-12-24
-- updated on 2025-12-29
