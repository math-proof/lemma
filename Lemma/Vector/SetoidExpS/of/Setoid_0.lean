import Lemma.Hyperreal.Infinitesimal.is.Setoid_0
import Lemma.Hyperreal.SetoidExpS.of.InfinitesimalSub
import Lemma.Vector.GetSub.eq.SubGetS
import Lemma.Vector.Setoid.is.All_SetoidGetS
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
  apply Setoid.of.All_SetoidGetS.fin
  intro i
  simp
  apply SetoidExpS.of.InfinitesimalSub
  apply Infinitesimal.of.Setoid_0
  rw [SubGetS.eq.GetSub.fin]
  have h := All_SetoidGetS.of.Setoid.fin h i
  rwa [EqGet0_0.fin] at h


-- created on 2025-12-24
-- updated on 2025-12-29
