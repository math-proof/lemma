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


-- created on 2025-07-12
-- updated on 2025-09-24
