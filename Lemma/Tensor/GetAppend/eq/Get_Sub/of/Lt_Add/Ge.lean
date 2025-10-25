import sympy.tensor.tensor
import Lemma.Nat.LtSub.is.Lt_Add.of.Ge
import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.List.AddProdSCons.eq.MulAdd
import Lemma.Vector.SEqArraySliceS.of.SEq.Eq.Eq
import Lemma.Vector.Unflatten.eq.AppendUnflattenS.of.SEq_Append
import Lemma.Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
import Lemma.Bool.EqCast.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.Vector.GetUnflatten.as.ArraySlice.of.Lt
import Lemma.Nat.Gt_0.of.Lt_Add.Ge
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten.of.Lt
import Lemma.Vector.GetSplitAt_1.as.ArraySlice.of.Lt_Get_0.GtLength_0
import Lemma.Vector.ArraySlice.as.GetCast_SplitAt_1.of.Lt_Get_0.GtLength_0.Eq_ProdTail.Eq_Prod
open Vector List Bool Nat


@[main]
private lemma main
-- given
  (h₀ : i ≥ m)
  (h₁ : i < m + n)
  (a : Tensor α (m :: s))
  (b : Tensor α (n :: s)) :
-- imply
  let h_i : i - m < n := LtSub.of.Lt_Add.Ge h₀ h₁
  (a ++ b)[i] = b[i - m] := by
-- proof
  simp [GetElem.getElem]
  simp [Tensor.get]
  ·
    simp [HAppend.hAppend]
    simp [Tensor.append]
    simp [Tensor.toVector]
    have h := Gt_0.of.Lt_Add.Ge h₀ h₁
    have h_lt := LtSub.of.Lt_Add.Ge h₀ h₁
    repeat rw [GetCast_Map.eq.UFnGet.of.Eq.Lt (by simp_all) (by simp_all)]
    simp
    apply Eq.of.SEq
    apply SEq.of.SEq.SEq (c := b.data.unflatten[i - m])
    ·
      have h_prod := AddProdSCons.eq.MulAdd m n s
      apply SEq.of.SEq.SEq (c := (a.data ++ b.data).array_slice (i * s.prod) s.prod)
      ·
        have h : List.Vector α ((m :: s).prod + (n :: s).prod) = List.Vector α ((m + n) :: s).prod := by
          simp_all
        have := GetSplitAt_1.as.ArraySlice.of.Lt_Get_0.GtLength_0 (s := (m + n) :: s) (by simp) h₁ (cast h (a.data ++ b.data))
        apply SEq.of.SEq.SEq this
        apply SEq.symm
        apply this.symm.trans
        apply GetCast_SplitAt_1.as.ArraySlice.of.Lt_Get_0.GtLength_0.Eq_ProdTail.Eq_Prod <;>
          simp_all
      ·
        simp at h_prod
        let ab : List.Vector α ((m + n) * s.prod) := cast (by simp_all) (a.data ++ b.data)
        have h_ab : ab ≃ a.data ++ b.data := by
          simp [ab]
          apply SEqCast.of.Eq h_prod
        apply SEq.of.SEq.SEq (c := ab.unflatten[i])
        ·
          rw [Unflatten.eq.AppendUnflattenS.of.SEq_Append h_ab]
          rw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge (by simp_all) (by simp_all)]
          rfl
        ·
          apply SEq.of.SEq.SEq (c := ab.array_slice (i * s.prod) s.prod)
          ·
            apply SEqArraySliceS.of.SEq.Eq.Eq rfl rfl
            simp [ab]
            apply SEq_Cast.of.SEq.Eq (by assumption)
            apply SEq.of.Eq rfl
          ·
            apply GetUnflatten.as.ArraySlice.of.Lt (by assumption)
    ·
      have := GetUnflatten.eq.GetSplitAt_1.of.Lt h_lt b.data
      simp at this
      rw [this]


-- created on 2025-06-01
-- updated on 2025-07-17
