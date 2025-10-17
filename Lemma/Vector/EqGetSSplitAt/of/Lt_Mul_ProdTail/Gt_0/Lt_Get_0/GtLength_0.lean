import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.Div_Mul_ProdDrop.lt.ProdTake.of.Lt_Mul_ProdTail.Lt_Get_0.GtLength_0
import Lemma.List.ModAddMulProdTail.lt.ProdDrop.of.Lt_Mul_ProdTail.Lt_Get_0.GtLength_0
import Lemma.List.Div_Mul_ProdDrop.lt.ProdTakeDrop_1.of.Lt_Mul_ProdTail.GtVal_0
import Lemma.List.ModProdDrop.lt.ProdDropDrop_1.of.Lt_Mul_ProdTail.GtVal_0
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.Vector.EqGetS.of.Eq.Lt
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.MulDiv.eq.Sub_Mod
import Lemma.Algebra.Dvd_Mul
import Lemma.Nat.Gt_0.of.GtMul
import Lemma.List.ProdDrop.dvd.ProdTail.of.Gt_0
import Lemma.Nat.DivAdd.eq.AddDivS.of.Dvd
import Lemma.Nat.DivMul.eq.Mul_Div.of.Dvd
import Lemma.Algebra.EqDivMul.of.Ne_0
import Lemma.Nat.ModAdd.eq.Mod.of.Dvd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqAddS.is.Eq
import Lemma.Algebra.SubAdd.eq.Add_Sub.of.Ge
import Lemma.Nat.Ge_Mod
import Lemma.Algebra.Dvd_Mul.of.Dvd
open Algebra Vector List Nat


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (h_d : d > 0)
  (h_t : t < n * s.tail.prod)
  (v : List.Vector α s.prod) :
-- imply
  have := Div_Mul_ProdDrop.lt.ProdTake.of.Lt_Mul_ProdTail.Lt_Get_0.GtLength_0 h_s h_i h_t d
  have := ModAddMulProdTail.lt.ProdDrop.of.Lt_Mul_ProdTail.Lt_Get_0.GtLength_0 h_s h_i h_t d
  have : i < (s.take 1).prod := by rwa [ProdTake_1.eq.Get_0.of.GtLength_0 h_s]
  have := Div_Mul_ProdDrop.lt.ProdTakeDrop_1.of.Lt_Mul_ProdTail.GtVal_0 h_d h_t
  have := ModProdDrop.lt.ProdDropDrop_1.of.Lt_Mul_ProdTail.GtVal_0 h_d h_t
  (v.splitAt d)[(i * (n * s.tail.prod) + t) / (n * (s.drop d).prod)][(i * (n * s.tail.prod) + t) % (s.drop d).prod] = ((v.splitAt 1)[i].splitAt (d - 1))[t / (n * (s.drop d).prod)][t % (s.drop d).prod] := by
-- proof
  intro h_it h_mod_it h_i' h_t' h_mod_t
  repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop]
  apply EqGetS.of.Eq.Lt.nat
  simp
  rw [EqAddSub.of.Ge (by linarith)]
  rw [Div_Mul.eq.DivDiv]
  rw [MulDiv.eq.Sub_Mod]
  have := Dvd_Mul.left n s.tail.prod
  have := Gt_0.of.GtMul.left h_t
  have := ProdDrop.dvd.ProdTail.of.Gt_0 h_d s
  rw [DivAdd.eq.AddDivS.of.Dvd]
  ·
    rw [DivMul.eq.Mul_Div.of.Dvd (by assumption)]
    rw [EqDivMul.of.Ne_0.left (by linarith)]
    repeat rw [ModAdd.eq.Mod.of.Dvd.left]
    ·
      rw [Add_Add.eq.AddAdd]
      apply EqAddS.of.Eq
      rw [SubAdd.eq.Add_Sub.of.Ge]
      ·
        apply EqAddS.of.Eq.left
        rw [Div_Mul.eq.DivDiv]
        rw [MulDiv.eq.Sub_Mod]
      ·
        apply Ge_Mod
    ·
      repeat apply Dvd_Mul.of.Dvd
      assumption
    ·
      apply Dvd_Mul.of.Dvd
      assumption
  ·
    apply Dvd_Mul.of.Dvd
    assumption


-- created on 2025-07-07
