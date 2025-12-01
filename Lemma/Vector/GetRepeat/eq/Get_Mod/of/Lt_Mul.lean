import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Nat.Gt_0.of.GtMul
open Vector Nat


@[main]
private lemma main
-- given
  (h : k < t * n)
  (v : List.Vector α n) :
-- imply
  have := LtMod.of.Gt_0 (Gt_0.of.GtMul h) k
  (v.repeat t)[k] = v[k % n] := by
-- proof
  have := GetRepeat.eq.Get_Mod v ⟨k, h⟩
  simpa


@[main]
private lemma fin
-- given
  (h : k < t * n)
  (v : List.Vector α n) :
-- imply
  (v.repeat t).get ⟨k, h⟩ = v.get ⟨k % n, LtMod.of.Gt_0 (Gt_0.of.GtMul h) k⟩ := by
-- proof
  apply main h


-- created on 2025-07-12
-- updated on 2025-09-24
