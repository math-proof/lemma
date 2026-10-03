import Lemma.Tensor.SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Ite_Block
import Lemma.Tensor.XEqDotS.of.XEq
import Lemma.Tensor.XEqGetS.of.XEq.GtLength
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.MapDot.eq.DotMapS.of.All_Eq_Add.All_Eq_Mul
import Lemma.Tensor.Dot.eq.Stack_Sum_MulGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.XEq.of.Eq
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.XEq.is.All_XEqGetS.of.GtLength_0
import Lemma.Tensor.Eq.is.EqDataS
import sympy.Basic
open Tensor Hyperreal
set_option maxHeartbeats 2000000


private lemma sum_sc {m : ℕ} (h : Fin m → ℝ) : ((∑ k, h k : ℝ) : Tensor ℝ []) = ∑ k, ((h k : ℝ) : Tensor ℝ []) := by
  let φ : ℝ →+ Tensor ℝ [] := AddMonoidHom.mk' (fun x => (x : Tensor ℝ [])) (fun x y => by apply Eq.of.EqDataS; rfl)
  exact map_sum φ h Finset.univ


private lemma real_row
  {m d : ℕ}
  (b : Fin m → ℝ)
  (v : Fin m → Fin d → ℝ) :
  (([j < m] ((b j : ℝ) : Tensor ℝ [])) : Tensor ℝ [m]) @ (([j < m] [l < d] ((v j l : ℝ) : Tensor ℝ [])) : Tensor ℝ [m, d]) =
    [l < d] (((∑ j, b j * v j l : ℝ)) : Tensor ℝ []) := by
  rw [Dot.eq.Stack_Sum_MulGetS.vm]
  congr 1
  funext l
  rw [sum_sc]
  congr 1
  funext k
  have h1 : ([j < m] ((b j : ℝ) : Tensor ℝ []))[k] = ((b k : ℝ) : Tensor ℝ []) := EqGetStack.fin (fun j => ((b j : ℝ) : Tensor ℝ [])) k
  have h2 : (([j < m] [l < d] ((v j l : ℝ) : Tensor ℝ [])) : Tensor ℝ [m, d])[k][l] = ((v k l : ℝ) : Tensor ℝ []) := by
    have := EqGetStack.fin (fun j => ([l < d] ((v j l : ℝ) : Tensor ℝ []) : Tensor ℝ [d])) k
    simp only [GetElem.getElem] at this ⊢
    erw [this]
    exact EqGetStack.fin (fun l => ((v k l : ℝ) : Tensor ℝ [])) l
  simp only [id]
  rw [h1, h2]
  apply Eq.of.EqDataS
  rfl


/--
Row of a hyperreal masked softmax times a matrix of values.
For logits \( a_{ij} \), a mask \( P \) leaving every row at least one unmasked entry, weights \( w_{ij} \) with
\( w_{ij} = e^{a_{ij}} / \sum_{k : P_{ik}} e^{a_{ik}} \) on the unmasked entries, and values \( v_{ij\ell} \) (which may depend on the row \( i \)):
\[
\operatorname{softmax}(a + ([P] - 1)\infty)_i \, V_i \approx \Bigl[ \sum_j [P_{ij}]\, w_{ij}\, v_{ij\ell} \Bigr]_\ell .
\]
-/
@[main]
private lemma row
  {n m d : ℕ}
-- given
  (P : Fin n → Fin m → Prop)
  [∀ i j, Decidable (P i j)]
  (a w : Fin n → Fin m → ℝ)
  (v : Fin n → Fin m → Fin d → ℝ)
  (h_ne : ∀ i : Fin n, ∃ j : Fin m, P i j)
  (h : ∀ i j, P i j → w i j = Real.exp (a i j) / ∑ k ∈ Finset.univ.filter (fun k => P i k), Real.exp (a i k))
  (i : Fin n) :
-- imply
  let Ξ : Tensor ℝ* [n, m] := [i < n] [j < m] (Bool.toNat (decide (P i j)))
  let A : Tensor ℝ* [n, m] := ([i < n] [j < m] (a i j : Tensor ℝ []) : Tensor ℝ [n, m])
  let Vᵢ : Tensor ℝ [m, d] := [j < m] [l < d] (v i j l : Tensor ℝ [])
  ((A + (Ξ - 1) * ∞).softmax.get ⟨i, by grind⟩) @ (Vᵢ : Tensor ℝ* [m, d]) ≈
    ((([l < d] ((∑ j, (if P i j then w i j else 0) * v i j l : ℝ) : Tensor ℝ [])) : Tensor ℝ [d]) : Tensor ℝ* [d]) := by
-- proof
  intro Ξ A Vᵢ
  have h0 := SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Ite_Block P a w h_ne h
  have h1 := XEqGetS.of.XEq.GtLength.fin (i := i) (by grind) h0
  let X : Tensor ℝ [n, m] := [i < n] [j < m] (((if P i j then w i j else 0 : ℝ) : Tensor ℝ []))
  let B : Tensor ℝ [m] := [j < m] (((if P i j then w i j else 0 : ℝ)) : Tensor ℝ [])
  have h2 : ((X : Tensor ℝ* [n, m])).get ⟨i, by grind⟩ = (B : Tensor ℝ* [m]) := by
    have e1 : ((X : Tensor ℝ* [n, m])).get ⟨i, by grind⟩ = ((id (α := Tensor ℝ [m]) (X.get i) : Tensor ℝ [m]) : Tensor ℝ* [m]) :=
      GetMap.eq.MapGet.fin X Hyperreal.ofReal ⟨i, by simp [Tensor.length]⟩
    rw [e1]
    congr 1
    exact EqGetStack.fin (fun i : Fin n => ([j < m] (((if P i j then w i j else 0 : ℝ) : Tensor ℝ [])) : Tensor ℝ [m])) i
  rw [h2] at h1
  have h3 := XEqDotS.of.XEq (X := Vᵢ) h1
  have h4 : (B : Tensor ℝ* [m]) @ (Vᵢ : Tensor ℝ* [m, d]) = ((id (α := Tensor ℝ [d]) (B @ Vᵢ) : Tensor ℝ [d]) : Tensor ℝ* [d]) := by
    have := MapDot.eq.DotMapS.of.All_Eq_Add.All_Eq_Mul (f := Hyperreal.ofReal) (fun a b => Hyperreal.coe_mul a b) (fun a b => Hyperreal.coe_add a b) B Vᵢ
    exact this.symm
  rw [real_row] at h4
  exact h3.trans (Tensor.XEq.of.Eq h4)


/--
Matrix form of  when the values \( v_{j\ell} \) do not depend on the row:
\[
\operatorname{softmax}(a + ([P] - 1)\infty)\, V \approx \Bigl[ \sum_j [P_{ij}]\, w_{ij}\, v_{j\ell} \Bigr]_{i\ell} .
\]
-/
@[main]
private lemma main
  {n m d : ℕ}
-- given
  (P : Fin n → Fin m → Prop)
  [∀ i j, Decidable (P i j)]
  (a w : Fin n → Fin m → ℝ)
  (v : Fin m → Fin d → ℝ)
  (h_ne : ∀ i : Fin n, ∃ j : Fin m, P i j)
  (h : ∀ i j, P i j → w i j = Real.exp (a i j) / ∑ k ∈ Finset.univ.filter (fun k => P i k), Real.exp (a i k)) :
-- imply
  let Ξ : Tensor ℝ* [n, m] := [i < n] [j < m] (Bool.toNat (decide (P i j)))
  let A : Tensor ℝ* [n, m] := ([i < n] [j < m] (a i j : Tensor ℝ []) : Tensor ℝ [n, m])
  let V : Tensor ℝ [m, d] := [j < m] [l < d] (v j l : Tensor ℝ [])
  (A + (Ξ - 1) * ∞).softmax @ (V : Tensor ℝ* [m, d]) ≈
    ((([i < n] [l < d] ((∑ j, (if P i j then w i j else 0) * v j l : ℝ) : Tensor ℝ [])) : Tensor ℝ [n, d]) : Tensor ℝ* [n, d]) := by
-- proof
  intro Ξ A V
  apply XEq.of.All_XEqGetS.GtLength_0 (h := by simp [matmul_shape])
  intro i'
  have hi : (i' : ℕ) < n := i'.isLt
  let i : Fin n := ⟨i', hi⟩
  have h0 := row P a w (fun i => v) h_ne h i
  have e1 : ((A + (Ξ - 1) * ∞).softmax @ (V : Tensor ℝ* [m, d])).get i' = ((A + (Ξ - 1) * ∞).softmax.get i) @ (V : Tensor ℝ* [m, d]) :=
    GetDot.eq.DotGet.fin _ _ i
  let Y : Tensor ℝ [n, d] := [i < n] [l < d] ((∑ j, (if P i j then w i j else 0) * v j l : ℝ) : Tensor ℝ [])
  have e2 : ((Y : Tensor ℝ* [n, d])).get i' = ((id (α := Tensor ℝ [d]) (Y.get i) : Tensor ℝ [d]) : Tensor ℝ* [d]) :=
    GetMap.eq.MapGet.fin Y Hyperreal.ofReal i
  have e3 : Y.get i = ([l < d] ((∑ j, (if P i j then w i j else 0) * v j l : ℝ) : Tensor ℝ []) : Tensor ℝ [d]) :=
    EqGetStack.fin (fun i : Fin n => ([l < d] ((∑ j, (if P i j then w i j else 0) * v j l : ℝ) : Tensor ℝ []) : Tensor ℝ [d])) i
  have e4 : ((Y : Tensor ℝ* [n, d])).get i' = ((([l < d] ((∑ j, (if P i j then w i j else 0) * v j l : ℝ) : Tensor ℝ [])) : Tensor ℝ [d]) : Tensor ℝ* [d]) := by
    rw [e2]
    simp only [id]
    rw [e3]
  exact (Tensor.XEq.of.Eq e1).trans (h0.trans (Tensor.XEq.of.Eq e4.symm))


-- created on 2026-10-01
