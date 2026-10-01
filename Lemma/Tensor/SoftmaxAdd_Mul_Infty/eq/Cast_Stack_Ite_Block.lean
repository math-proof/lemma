import Lemma.Tensor.SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Ite_Div_Sum
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetExp.eq.ExpGet
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetDiv.eq.DivGet
import Lemma.Tensor.Sum_0.eq.Sum_Get
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.MapStack.eq.Stack_Map
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.XEqGetS.of.XEq.GtLength
import Lemma.Tensor.XEq.is.All_XEqGetS.of.GtLength_0
import Lemma.Tensor.XEq.of.Eq
import Lemma.Tensor.MapExp.eq.ExpMap.of.All_EqUFnExp_ExpUFn
import Lemma.Tensor.MapMul.eq.MulMapS.of.All_Eq_Mul
import Lemma.Tensor.MapDiv.eq.DivMapS.of.All_Eq_Div
import Lemma.Tensor.SumMap.eq.MapSum.of.All_EqUFnAdd
import Lemma.Hyperreal.OfRealExp.eq.ExpOfReal
import sympy.Basic
open Tensor Hyperreal


private lemma sc_ext {x y : ℝ} (h : x = y) : (x : Tensor ℝ []) = (y : Tensor ℝ []) := by rw [h]


/--
Block form of the hyperreal masked softmax, as used by the banded (`upper_triangle`, `lower_triangle`, ...) lemmas.
For logits \( a_{ij} \in \mathbb{R} \), a mask \( P \) leaving every row at least one unmasked entry, and
weights \( w_{ij} \) which on the unmasked entries are \( e^{a_{ij}} / \sum_{k : P_{ik}} e^{a_{ik}} \):
\[
\operatorname{softmax}(a + ([P] - 1)\infty) \approx \bigl[ [P_{ij}]\, w_{ij} \bigr]_{ij}.
\]
-/
@[main]
private lemma main
  {n m : ℕ}
-- given
  (P : Fin n → Fin m → Prop)
  [∀ i j, Decidable (P i j)]
  (a w : Fin n → Fin m → ℝ)
  (h_ne : ∀ i : Fin n, ∃ j : Fin m, P i j)
  (h : ∀ i j, P i j → w i j = Real.exp (a i j) / ∑ k ∈ Finset.univ.filter (fun k => P i k), Real.exp (a i k)) :
-- imply
  let Ξ : Tensor ℝ* [n, m] := [i < n] [j < m] (Bool.toNat (decide (P i j)))
  let A : Tensor ℝ* [n, m] := ([i < n] [j < m] (a i j : Tensor ℝ []) : Tensor ℝ [n, m])
  (A + (Ξ - 1) * ∞).softmax ≈
    (([i < n] [j < m] (((if P i j then w i j else 0 : ℝ) : Tensor ℝ [])) : Tensor ℝ [n, m]) : Tensor ℝ* [n, m]) := by
-- proof
  intro Ξ A
  have h0 := SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Ite_Div_Sum (fun i j => decide (P i j)) a (fun i => by
    obtain ⟨j, hj⟩ := h_ne i
    exact ⟨j, by simpa using hj⟩)
  refine h0.trans (Tensor.XEq.of.Eq ?_)
  congr 1
  congr 1
  funext i
  congr 1
  funext j
  apply sc_ext
  by_cases hp : P i j
  · simp only [hp, decide_true, if_true]
    rw [h i j hp, Finset.sum_filter]
    simp
  · simp [hp]


/--
Log form of `main`: the weights are given through \( z_{ij} = a_{ij} - \log \sum_{k : P_{ik}} e^{a_{ik}} \) on the unmasked entries, so that
\[
\operatorname{softmax}(a + ([P] - 1)\infty) \approx \bigl[ [P_{ij}]\, e^{z_{ij}} \bigr]_{ij}.
\]
-/
@[main]
private lemma log
  {n m : ℕ}
-- given
  (P : Fin n → Fin m → Prop)
  [∀ i j, Decidable (P i j)]
  (a z : Fin n → Fin m → ℝ)
  (h_ne : ∀ i : Fin n, ∃ j : Fin m, P i j)
  (h : ∀ i j, P i j → z i j = a i j - Real.log (∑ k ∈ Finset.univ.filter (fun k => P i k), Real.exp (a i k))) :
-- imply
  let Ξ : Tensor ℝ* [n, m] := [i < n] [j < m] (Bool.toNat (decide (P i j)))
  let A : Tensor ℝ* [n, m] := ([i < n] [j < m] (a i j : Tensor ℝ []) : Tensor ℝ [n, m])
  (A + (Ξ - 1) * ∞).softmax ≈
    (([i < n] [j < m] (((if P i j then Real.exp (z i j) else 0 : ℝ) : Tensor ℝ [])) : Tensor ℝ [n, m]) : Tensor ℝ* [n, m]) := by
-- proof
  have hpos : ∀ i j, P i j → 0 < ∑ k ∈ Finset.univ.filter (fun k => P i k), Real.exp (a i k) := by
    intro i j hp
    exact Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hp⟩⟩
  exact main P a (fun i j => Real.exp (z i j)) h_ne (fun i j hp => by
    rw [h i j hp, Real.exp_sub, Real.exp_log (hpos i j hp)])


-- created on 2026-10-01
