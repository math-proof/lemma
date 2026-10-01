import Lemma.Tensor.SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Ite_Block
import Lemma.Hyperreal.XEqCoeLog.of.XEqCoe.Ne_0
import Lemma.Tensor.XEqGetS.of.XEq.GtLength
import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Vector.XEq.is.All_XEqGetS
import Lemma.Vector.GetLog.eq.LogGet
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.EqGetStack
import sympy.Basic
open Tensor Hyperreal
set_option maxHeartbeats 1000000

private lemma log_scalar {X : Tensor ℝ* []} {r : ℝ} (h_r : r ≠ 0)
    (h : X ≈ (((r : ℝ) : Tensor ℝ []) : Tensor ℝ* [])) :
    Log.log X ≈ ((((Real.log r : ℝ)) : Tensor ℝ []) : Tensor ℝ* []) := by
  have h' : X.data ≈ (((r : ℝ) : Tensor ℝ []) : Tensor ℝ* []).data := h
  apply (Tensor.XEq.is.XEqDataS _ _).mpr
  have hl : (Log.log X).data = Log.log X.data := rfl
  rw [hl]
  apply Vector.XEq.of.All_XEqGetS.fin
  intro i
  rw [Vector.GetLog.eq.LogGet.fin]
  have hi : i.val = 0 := by have := i.2; simpa using this
  have i0 : i = ⟨0, by simp⟩ := Fin.ext hi
  subst i0
  have h0 := Vector.All_XEqGetS.of.XEq.fin h' ⟨0, by simp⟩
  have h1 : X.data.get ⟨0, by simp⟩ ≈ ((r : ℝ) : ℝ*) := h0
  exact XEqCoeLog.of.XEqCoe.Ne_0 h_r h1

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
Entry of the hyperreal masked softmax (log form): for \( z_{ij} = a_{ij} - \log \sum_{k : P_{ik}} e^{a_{ik}} \) and an unmasked entry \( P_{ij} \),
\[
\log \operatorname{softmax}(a + ([P] - 1)\infty)_{ij} \approx z_{ij}.
\]
-/
@[main]
private lemma main
  {n m : ℕ}
-- given
  (P : Fin n → Fin m → Prop)
  [∀ i j, Decidable (P i j)]
  (a z : Fin n → Fin m → ℝ)
  (h_ne : ∀ i : Fin n, ∃ j : Fin m, P i j)
  (h : ∀ i j, P i j → z i j = a i j - Real.log (∑ k ∈ Finset.univ.filter (fun k => P i k), Real.exp (a i k)))
  (i : Fin n)
  (j : Fin m)
  (h_P : P i j) :
-- imply
  let Ξ : Tensor ℝ* [n, m] := [i < n] [j < m] (Bool.toNat (decide (P i j)))
  let A : Tensor ℝ* [n, m] := ([i < n] [j < m] (a i j : Tensor ℝ []) : Tensor ℝ [n, m])
  Log.log (((A + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ : Tensor ℝ* []) ≈ (((z i j : ℝ) : Tensor ℝ []) : Tensor ℝ* []) := by
-- proof
  intro Ξ A
  have h0 := SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Ite_Block.log P a z h_ne h
  have h1 := XEqGetS.of.XEq.GtLength.fin (i := i) (by simp [Tensor.length]) h0
  have h2 := XEqGetS.of.XEq.GtLength.fin (i := j) (by simp [Tensor.length]) h1
  have he := entry (fun i j => if P i j then Real.exp (z i j) else 0) i j
  have h3 : ((A + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ ≈
      (((Real.exp (z i j) : ℝ) : Tensor ℝ []) : Tensor ℝ* []) := by
    have h2' : ((A + (Ξ - 1) * ∞).softmax.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ ≈
        (((if P i j then Real.exp (z i j) else 0 : ℝ) : Tensor ℝ []) : Tensor ℝ* []) := by
      rw [← he]
      exact h2
    simpa [h_P] using h2'
  have h4 := log_scalar (Real.exp_ne_zero (z i j)) h3
  rw [Real.log_exp] at h4
  exact h4


-- created on 2026-10-01
