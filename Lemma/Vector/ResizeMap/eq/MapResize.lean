import Lemma.Nat.LtMod.of.Lt_Mul
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.GetResize.eq.Ite_Get_Mod
open Nat Vector


@[main, comm]
private lemma main
  [Zero α] [Zero β]
  {f : α → β}
-- given
  (h0 : f 0 = 0)
  (v : List.Vector α n)
  (m : ℕ) :
-- imply
  (v.map f).resize m = (v.resize m).map f := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  have hL : ((v.map f).resize m)[i] = if h : ↑i < m / n * n then (v.map f)[↑i % n]'(LtMod.of.Lt_Mul h) else 0 :=
    GetResize.eq.Ite_Get_Mod.fin (v.map f) m i
  have hR : (v.resize m)[i] = if h : ↑i < m / n * n then v[↑i % n]'(LtMod.of.Lt_Mul h) else 0 :=
    GetResize.eq.Ite_Get_Mod.fin v m i
  change ((v.map f).resize m)[i] = ((v.resize m).map f)[i]
  rw [hL]
  have hmap : ((v.resize m).map f)[i] = f (v.resize m)[i] := by
    change List.Vector.get _ i = _
    rw [List.Vector.get_map]
    rfl
  rw [hmap, hR]
  split_ifs <;> aesop


-- created on 2026-08-12
