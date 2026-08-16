import Lemma.List.EqSwap_0'1
import Lemma.Tensor.Dot.eq.Bmm
import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_SoftmaxGetSlice
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.GetGetSlice.eq.Get
import Lemma.Tensor.MapBmm.eq.BmmMapS.of.All_Eq_Add.All_Eq_Mul
import Lemma.Tensor.MapCast.as.Map.of.Eq
import Lemma.Tensor.MapDiv.eq.DivMap.of.All_Eq_Div
import Lemma.Tensor.TMap.eq.MapT
import Lemma.Tensor.XEq.of.Eq
open List Tensor
set_option maxHeartbeats 800000


@[main]
private lemma gpt
  [NeZero (n : ℕ)]
  [NeZero (d_z : ℕ)]
-- given
  (Q K V : Tensor ℝ [n, d_z]) :
-- imply
  let Q : Tensor ℝ* [n, d_z] := Q
  let K : Tensor ℝ* [n, d_z] := K
  let V : Tensor ℝ* [n, d_z] := V
  let QK : Tensor ℝ* [n, n] := Q @ Kᵀ
  (QK / √(d_z : ℝ*) + ((1 : Tensor ℝ* [n, n]).band_part n 0 - 1) * ∞).softmax @ V ≈ [i < n] (Q[i] @ K[:i + 1]ᵀ / √(d_z : ℝ*)).softmax @ V[:i + 1] := by
-- proof
  extract_lets Q' K' V' QK'
  have hshape :
      [n, d_z].swap ([n, d_z].length - 2) ([n, d_z].length - 1) = [d_z, n] := by
    simp [EqSwap_0'1]
  let KT : Tensor ℝ [d_z, n] := cast (congrArg (Tensor ℝ) hshape) Kᵀ
  let A : Tensor ℝ [n, n] := (Q @ KT) / √(d_z : ℝ)
  have h := DotSoftmaxAdd_Mul_Infty.eq.Stack_SoftmaxGetSlice A V
  have hscores :
      ((Q.map Hyperreal.ofReal).bmm (KT.map Hyperreal.ofReal) / Root.sqrt (d_z : Hyperreal)) =
        ((Q @ KT) / Root.sqrt (d_z : ℝ)).map Hyperreal.ofReal := by
    rw [MapDiv.eq.DivMap.of.All_Eq_Div (f := Hyperreal.ofReal) (fun a b => rfl)]
    congr 1
    rw [Dot.eq.Bmm]
    apply BmmMapS.eq.MapBmm.of.All_Eq_Add.All_Eq_Mul (f := Hyperreal.ofReal) <;> aesop
  have hKT :
      KT.map Hyperreal.ofReal =
        cast (congrArg (Tensor ℝ*) hshape) (K.map Hyperreal.ofReal)ᵀ := by
    simp only [KT]
    rw [MapCast.eq.Cast_Map.of.Eq hshape]
    rw [TMap.eq.MapT]
  have hQK :
      QK' = (Q.map Hyperreal.ofReal) @ (KT.map Hyperreal.ofReal) := by
    apply Eq.of.EqDataS
    simp only [QK', Q', K', KT, hKT]
    rfl
  have hdiv :
      QK' / √(d_z : ℝ*) = A.map Hyperreal.ofReal := by
    rw [hQK]
    simp only [A]
    rw [Dot.eq.Bmm]
    exact hscores
  refine (XEq.of.Eq ?lhs).trans (h.trans (XEq.of.Eq ?rhs))
  ·
    simp only [hdiv]
    rfl
  ·
    apply Eq.of.All_EqGetS.fin
    intro i
    rw [EqGetStack.fn.fin, EqGetStack.fn.fin]
    have hrow :
        (A.map Hyperreal.ofReal)[i][:i + 1] =
          Q'[i] @ K'[:i + 1]ᵀ / √(d_z : ℝ*) := by
      apply Eq.of.All_EqGetS.fin
      intro j
      have hL :=
        GetGetSlice.eq.Get.fin
          (X := (A.map Hyperreal.ofReal)[i])
          (n := (i : ℕ) + 1)
          j
      simp [GetElem.getElem] at hL ⊢
      rw [hL]
      sorry
    rw [hrow]
    rfl


-- created on 2023-06-18
-- updated on 2026-08-17
