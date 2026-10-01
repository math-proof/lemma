import Lemma.Tensor.SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Div_Sum
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
set_option maxHeartbeats 1000000

private lemma sum_sc {m : ℕ} (h : Fin m → ℝ) : ((∑ k, h k : ℝ) : Tensor ℝ []) = ∑ k, ((h k : ℝ) : Tensor ℝ []) := by
  let φ : ℝ →+ Tensor ℝ [] := AddMonoidHom.mk' (fun x => (x : Tensor ℝ [])) (fun x y => by apply Eq.of.EqDataS; rfl)
  exact map_sum φ h Finset.univ


private lemma sc_ext {x y : ℝ} (h : x = y) : (x : Tensor ℝ []) = (y : Tensor ℝ []) := by rw [h]


private lemma real_row {m : ℕ} (f g : Fin m → ℝ) :
    let X : Tensor ℝ [m] := [j < m] (f j : Tensor ℝ [])
    let Y : Tensor ℝ [m] := [j < m] (g j : Tensor ℝ [])
    (exp X * Y) / id (α := Tensor ℝ []) ((exp X * Y).sum 0) =
      ([j < m] (((Real.exp (f j) * g j) / ∑ k, (Real.exp (f k) * g k) : ℝ) : Tensor ℝ [])) := by
  intro X Y
  apply Eq.of.All_EqGetS.fin
  intro j
  have hd := GetDiv.eq.DivGet.fin (exp X * Y) (((exp X * Y).sum 0 : Tensor ℝ [])) j
  have hs := Sum_0.eq.Sum_Get.fin (exp X * Y)
  have hm := fun i => GetMul.eq.MulGetS.fin (exp X) Y i
  have he := fun i => GetExp.eq.ExpGet.fin X i
  have hX : ∀ i : Fin m, X.get i = (f i : Tensor ℝ []) := fun i => EqGetStack.fin (fun j => (f j : Tensor ℝ [])) i
  have hY : ∀ i : Fin m, Y.get i = (g i : Tensor ℝ []) := fun i => EqGetStack.fin (fun j => (g j : Tensor ℝ [])) i
  have hterm : ∀ i : Fin m, (exp X * Y).get i = ((Real.exp (f i) * g i : ℝ) : Tensor ℝ []) := by
    intro i
    rw [hm i]
    erw [he i]
    rw [hX i, hY i]
    rfl
  have hsum : ((exp X * Y).sum 0 : Tensor ℝ []) = ((∑ k, (Real.exp (f k) * g k) : ℝ) : Tensor ℝ []) := by
    rw [hs]
    simp only [hterm]
    exact (sum_sc _).symm
  simp only [id]
  erw [hd, hterm j, hsum]
  erw [EqGetStack.fin (fun j => (((Real.exp (f j) * g j) / ∑ k, (Real.exp (f k) * g k) : ℝ) : Tensor ℝ [])) j]
  rfl

private lemma sc_bool (b : Bool) : ((b.toNat : ℕ) : Tensor ℝ []) = (((b.toNat : ℕ) : ℝ) : Tensor ℝ []) := by
  apply Eq.of.EqDataS
  cases b <;> rfl


/--
Entrywise form of the hyperreal masked softmax: for logits \( a_{ij} \in \mathbb{R} \) and a mask \( p \) leaving
every row at least one unmasked entry,
\[
\operatorname{softmax}(a + ([p] - 1)\infty) \approx \Bigl[ [p_{ij}] \frac{e^{a_{ij}}}{\sum_{k} [p_{ik}] e^{a_{ik}}} \Bigr]_{ij}
\]
(the right side is a real tensor cast to \( \mathbb{R}^* \)).
-/
@[main]
private lemma main
  {n m : ℕ}
-- given
  (p : Fin n → Fin m → Bool)
  (a : Fin n → Fin m → ℝ)
  (h_ne : ∀ i : Fin n, ∃ j : Fin m, p i j = true) :
-- imply
  let Ξ : Tensor ℝ* [n, m] := [i < n] [j < m] (Bool.toNat (p i j))
  let A : Tensor ℝ* [n, m] := ([i < n] [j < m] (a i j : Tensor ℝ []) : Tensor ℝ [n, m])
  (A + (Ξ - 1) * ∞).softmax ≈
    (([i < n] [j < m] (((if p i j then Real.exp (a i j) / ∑ k, (if p i k then Real.exp (a i k) else 0) else 0 : ℝ) : Tensor ℝ [])) : Tensor ℝ [n, m]) : Tensor ℝ* [n, m]) := by
-- proof
  intro Ξ A
  let A₀ : Tensor ℝ [n, m] := [i < n] [j < m] (a i j : Tensor ℝ [])
  let Ξ₀ : Tensor ℝ [n, m] := [i < n] [j < m] (Bool.toNat (p i j))
  have h : (A + (Ξ - 1) * ∞).softmax ≈
      (([i < n] (exp A₀[i] * Ξ₀[i] / id (α := Tensor ℝ []) ((exp A₀[i] * Ξ₀[i]).sum 0)) : Tensor ℝ [n, m]) : Tensor ℝ* [n, m]) :=
    SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Div_Sum p A₀ h_ne
  refine h.trans (Tensor.XEq.of.Eq ?_)
  congr 1
  congr 1
  funext i
  have hA : A₀[i] = [j < m] (a i j : Tensor ℝ []) := EqGetStack.fin (fun i : Fin n => [j < m] (a i j : Tensor ℝ [])) i
  have hΞ : Ξ₀[i] = [j < m] (((p i j).toNat : ℝ) : Tensor ℝ []) := by
    have := EqGetStack.fin (fun i : Fin n => [j < m] (Bool.toNat (p i j) : Tensor ℝ [])) i
    refine this.trans ?_
    congr 1
  rw [hA, hΞ]
  refine (real_row (a i) (fun j => (((p i j).toNat : ℕ) : ℝ))).trans ?_
  congr 1
  funext j
  apply sc_ext
  have hs : ∀ k, Real.exp (a i k) * (((p i k).toNat : ℕ) : ℝ) = if p i k = true then Real.exp (a i k) else 0 := by
    intro k
    cases p i k <;> simp
  simp only [hs]
  cases hp : p i j <;> simp


-- created on 2026-10-01
