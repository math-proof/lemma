import Lemma.Tensor.SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Ite_Block
import Lemma.Tensor.XEqGetS.of.XEq.GtLength
import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Vector.XEq.is.All_XEqGetS
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.EqGetStack
import torch.Tensor.item
import sympy.Basic
open Tensor
set_option maxHeartbeats 1000000

private lemma entry {n m : ℕ} (f : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) :
    (((([i < n] [j < m] (((f i j : ℝ)) : Tensor ℝ []) : Tensor ℝ [n, m]) : Tensor ℝ* [n, m]).get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []) =
      (((f i j : ℝ) : Tensor ℝ []) : Tensor ℝ* []) := by
  have h1 := GetMap.eq.MapGet.fin ([i < n] [j < m] (((f i j : ℝ)) : Tensor ℝ []) : Tensor ℝ [n, m]) Hyperreal.ofReal ⟨i, by simp [Tensor.length]⟩
  have h2 := EqGetStack.fin (fun i : Fin n => [j < m] (((f i j : ℝ)) : Tensor ℝ [])) i
  have h3 := GetMap.eq.MapGet.fin ([j < m] (((f i j : ℝ)) : Tensor ℝ []) : Tensor ℝ [m]) Hyperreal.ofReal ⟨j, by simp [Tensor.length]⟩
  have h4 := EqGetStack.fin (fun j : Fin m => (((f i j : ℝ)) : Tensor ℝ [])) j
  erw [h1, h2]
  erw [h3, h4]
  rfl


/--
Scalar entry of the hyperreal masked softmax: for logits \( a_{ij} \), a mask \( P \) leaving every row at least one unmasked entry and weights \( w_{ij} = e^{a_{ij}} / \sum_{k : P_{ik}} e^{a_{ik}} \) on the unmasked entries,
\[
\operatorname{softmax}(a + ([P] - 1)\infty)_{ij} \approx [P_{ij}]\, w_{ij}.
\]
-/
@[path]
private lemma main
  {n m : ℕ}
-- given
  (P : Fin n → Fin m → Prop)
  [∀ i j, Decidable (P i j)]
  (a w : Fin n → Fin m → ℝ)
  (h_ne : ∀ i : Fin n, ∃ j : Fin m, P i j)
  (h : ∀ i j, P i j → w i j = Real.exp (a i j) / ∑ k ∈ Finset.univ.filter (fun k => P i k), Real.exp (a i k))
  (i : Fin n)
  (j : Fin m) :
-- imply
  let Ξ : Tensor ℝ* [n, m] := [i < n] [j < m] (Bool.toNat (decide (P i j)))
  let A : Tensor ℝ* [n, m] := ([i < n] [j < m] (a i j : Tensor ℝ []) : Tensor ℝ [n, m])
  (((A + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []).item ≈ (((if P i j then w i j else 0 : ℝ)) : ℝ*) := by
-- proof
  intro Ξ A
  have h0 := SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Ite_Block P a w h_ne h
  have h1 := XEqGetS.of.XEq.GtLength.fin (i := i) (by simp [Tensor.length]) h0
  have h2 := XEqGetS.of.XEq.GtLength.fin (i := j) (by simp [Tensor.length]) h1
  have he := entry (fun i j => if P i j then w i j else 0) i j
  rw [he] at h2
  have h3 : (((A + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩).data ≈
      (((((if P i j then w i j else 0 : ℝ)) : Tensor ℝ []) : Tensor ℝ* [])).data :=
    (Tensor.XEq.is.XEqDataS _ _).mp h2
  have h4 := Vector.All_XEqGetS.of.XEq.fin h3 ⟨0, by simp⟩
  exact h4


-- created on 2026-10-01