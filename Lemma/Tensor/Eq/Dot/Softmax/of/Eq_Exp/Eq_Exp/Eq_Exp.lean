import Lemma.Tensor.SoftmaxAdd_Mul_Infty.eq.Stack_Div_Sum
import sympy.Basic
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetExp.eq.ExpGet
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetDiv.eq.DivGet
import Lemma.Tensor.Sum_0.eq.Sum_Get
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.MapStack.eq.Stack_Map
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.DotDiv.eq.DivDot
import Lemma.Tensor.XEqDotS.of.XEq
import Lemma.Tensor.XEqGetS.of.XEq.GtLength
import Lemma.Tensor.XEq.is.All_XEqGetS.of.GtLength_0
import Lemma.Tensor.XEq.of.Eq
import Lemma.Tensor.MapExp.eq.ExpMap.of.All_EqUFnExp_ExpUFn
import Lemma.Tensor.MapMul.eq.MulMapS.of.All_Eq_Mul
import Lemma.Tensor.MapDiv.eq.DivMapS.of.All_Eq_Div
import Lemma.Tensor.SumMap.eq.MapSum.of.All_EqUFnAdd
import Lemma.Hyperreal.OfRealExp.eq.ExpOfReal
open Tensor Hyperreal
set_option maxHeartbeats 1000000


private lemma coe_scalar (b : Bool) :
    ((b.toNat : ℕ) : Tensor ℝ* []) = ((b.toNat : ℕ) : Tensor ℝ []).map Hyperreal.ofReal := by
  apply Eq.of.EqDataS
  cases b <;> rfl


private lemma coe_mask {n m : ℕ} (p : Fin n → Fin m → Bool) :
    ([i < n] [j < m] (Bool.toNat (p i j)) : Tensor ℝ* [n, m]) = (([i < n] [j < m] (Bool.toNat (p i j)) : Tensor ℝ [n, m]) : Tensor ℝ* [n, m]) := by
  rw [MapStack.eq.Stack_Map]
  congr 1
  funext i
  rw [MapStack.eq.Stack_Map]
  congr 1


private lemma row_cast {m : ℕ} (X Y : Tensor ℝ [m]) :
    (exp (X : Tensor ℝ* [m]) * (Y : Tensor ℝ* [m])) / id (α := Tensor ℝ* []) ((exp (X : Tensor ℝ* [m]) * (Y : Tensor ℝ* [m])).sum 0) =
      ((exp X * Y / id (α := Tensor ℝ []) ((exp X * Y).sum 0) : Tensor ℝ [m]) : Tensor ℝ* [m]) := by
  have hmul : ∀ a b : ℝ, Hyperreal.ofReal (a * b) = Hyperreal.ofReal a * Hyperreal.ofReal b := fun a b => Hyperreal.coe_mul a b
  have hdiv : ∀ a b : ℝ, Hyperreal.ofReal (a / b) = Hyperreal.ofReal a / Hyperreal.ofReal b := fun a b => Hyperreal.coe_div a b
  have hadd : ∀ a b : ℝ, Hyperreal.ofReal (a + b) = Hyperreal.ofReal a + Hyperreal.ofReal b := fun a b => Hyperreal.coe_add a b
  have hexp := MapExp.eq.ExpMap.of.All_EqUFnExp_ExpUFn (f := Hyperreal.ofReal) (fun x => OfRealExp.eq.ExpOfReal x) X
  change _ = (exp X * Y / id (α := Tensor ℝ []) ((exp X * Y).sum 0)).map Hyperreal.ofReal
  rw [MapDiv.eq.DivMapS.of.All_Eq_Div.scalar hdiv]
  rw [MapMul.eq.MulMapS.of.All_Eq_Mul hmul]
  have hs : ((exp X * Y).sum 0).map Hyperreal.ofReal = (((exp X * Y).map Hyperreal.ofReal).sum 0) := (SumMap.eq.MapSum.of.All_EqUFnAdd hadd _ 0).symm
  simp only [id]
  erw [hs]
  erw [MapMul.eq.MulMapS.of.All_Eq_Mul hmul (exp X) Y, hexp]

private lemma stack_div_dot
  {n m d : ℕ}
  (U : Fin n → Tensor ℝ* [m])
  (S : Fin n → Tensor ℝ* [])
  (V : Tensor ℝ* [m, d]) :
  (([i < n] (U i / S i) : Tensor ℝ* [n, m]) @ V) = [i < n] (((U i) @ V) / S i) := by
  apply Eq.of.All_EqGetS.fin
  intro i
  erw [GetDot.eq.DotGet.fin]
  erw [EqGetStack.fin (fun i => U i / S i) i]
  erw [EqGetStack.fin (fun i => ((U i) @ V) / S i) i]
  exact DotDiv.eq.DivDot (U i) (S i) V


/--
py: `softmax(Q @ K.T / sqrt(d_z) + (-1 + [[0, 1], [1, 0]] + Identity(n)) * oo) @ V`, where the block matrix has zeros on the
`h × h` and `(n-h) × (n-h)` diagonal blocks and ones elsewhere, and the identity adds the diagonal back, in the hyperreal masked softmax.
Written row by row with the mask `Ξ i j = [i = j ∨ ¬(i < h ↔ j < h)]`:
\[
\operatorname{softmax}(A + (\Xi - 1)\infty) V \approx \Bigl[\frac{(e^{A_i} \odot \Xi_i) V}{\sum_j e^{A_{ij}} \Xi_{ij}}\Bigr]_i,
\qquad A = \frac{Q K^{\top}}{\sqrt{d_z}} .
\]
Splitting off the diagonal term \( e^{A_{ii}} V_i \) from the cross block gives the block form of the py statement.
-/
@[path]
private lemma cross_attention
  {n h d_z : ℕ}
-- given
  (_h₀ : 0 < h)
  (_h₁ : h < n)
  (Q K V : Tensor ℝ [n, d_z]) :
-- imply
  let A : Tensor ℝ [n, n] := Q @ Kᵀ / √(d_z : ℝ)
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide (i = j ∨ ¬(i.val < h ↔ j.val < h))))
  let A : Tensor ℝ* [n, n] := A
  let V : Tensor ℝ* [n, d_z] := V
  (A + (Ξ - 1) * ∞).softmax @ V ≈ [i < n]
    ((exp A[i] * Ξ[i]) @ V) / id (α := Tensor ℝ* []) ((exp A[i] * Ξ[i]).sum 0) := by
-- proof
  intro A₀ Ξ A' V'
  have h_ne : ∀ i : Fin n, ∃ j : Fin n, (fun (i j : Fin n) => decide (i = j ∨ ¬(i.val < h ↔ j.val < h))) i j = true := by
    intro i
    exact ⟨i, by simp⟩
  have hmain : (A' + (Ξ - 1) * ∞).softmax ≈ [i < n] (exp A'[i] * Ξ[i] / id (α := Tensor ℝ* []) ((exp A'[i] * Ξ[i]).sum 0)) := SoftmaxAdd_Mul_Infty.eq.Stack_Div_Sum (fun (i j : Fin n) => decide (i = j ∨ ¬(i.val < h ↔ j.val < h))) A₀ h_ne
  let Ξ₀ : Tensor ℝ [n, n] := [i < n] [j < n] (Bool.toNat (decide (i = j ∨ ¬(i.val < h ↔ j.val < h))))
  have hΞ : Ξ = (Ξ₀ : Tensor ℝ* [n, n]) := coe_mask _
  have hrow : ∀ i : Fin n, exp A'[i] * Ξ[i] / id (α := Tensor ℝ* []) ((exp A'[i] * Ξ[i]).sum 0) =
      ((id (α := Tensor ℝ [n]) (exp A₀[i] * Ξ₀[i] / id (α := Tensor ℝ []) ((exp A₀[i] * Ξ₀[i]).sum 0)) : Tensor ℝ [n]) : Tensor ℝ* [n]) := by
    intro i
    have h1 : A'[i] = ((id (α := Tensor ℝ [n]) A₀[i] : Tensor ℝ [n]) : Tensor ℝ* [n]) := by
      exact GetMap.eq.MapGet.fin A₀ Hyperreal.ofReal ⟨i, by simp [Tensor.length]⟩
    have h2 : Ξ[i] = ((id (α := Tensor ℝ [n]) Ξ₀[i] : Tensor ℝ [n]) : Tensor ℝ* [n]) := by
      rw [hΞ]
      exact GetMap.eq.MapGet.fin Ξ₀ Hyperreal.ofReal ⟨i, by simp [Tensor.length]⟩
    rw [h1, h2]
    exact row_cast (id (α := Tensor ℝ [n]) A₀[i]) (id (α := Tensor ℝ [n]) Ξ₀[i])
  have hB : ([i < n] (exp A'[i] * Ξ[i] / id (α := Tensor ℝ* []) ((exp A'[i] * Ξ[i]).sum 0))) =
      ((([i < n] (id (α := Tensor ℝ [n]) (exp A₀[i] * Ξ₀[i] / id (α := Tensor ℝ []) ((exp A₀[i] * Ξ₀[i]).sum 0)))) : Tensor ℝ [n, n]) : Tensor ℝ* [n, n]) := by
    refine (congrArg (fun f => ([i < n] f i : Tensor ℝ* [n, n])) (funext hrow)).trans ?_
    symm
    exact MapStack.eq.Stack_Map (f := Hyperreal.ofReal) (fun i : Fin n => (id (α := Tensor ℝ [n]) (exp A₀[i] * Ξ₀[i] / id (α := Tensor ℝ []) ((exp A₀[i] * Ξ₀[i]).sum 0)))) 
  apply @Tensor.XEq.of.All_XEqGetS.fin
  intro i
  have hi : (i : ℕ) < n := i.isLt
  have hrow_i : ((A' + (Ξ - 1) * ∞).softmax).get ⟨i, by grind⟩ ≈ ((id (α := Tensor ℝ [n]) (exp A₀[i] * Ξ₀[i] / id (α := Tensor ℝ []) ((exp A₀[i] * Ξ₀[i]).sum 0)) : Tensor ℝ [n]) : Tensor ℝ* [n]) := by
    have h0 := XEqGetS.of.XEq.GtLength.fin (i := i) (by grind) hmain
    have h1 : ([i < n] (exp A'[i] * Ξ[i] / id (α := Tensor ℝ* []) ((exp A'[i] * Ξ[i]).sum 0))).get ⟨i, by grind⟩ = exp A'[i] * Ξ[i] / id (α := Tensor ℝ* []) ((exp A'[i] * Ξ[i]).sum 0) :=
      EqGetStack.fin (fun i : Fin n => exp A'[i] * Ξ[i] / id (α := Tensor ℝ* []) ((exp A'[i] * Ξ[i]).sum 0)) i
    exact h0.trans (Tensor.XEq.of.Eq (h1.trans (hrow i)))
  have hl : ((A' + (Ξ - 1) * ∞).softmax @ V').get i = ((A' + (Ξ - 1) * ∞).softmax.get ⟨i, by grind⟩) @ V' :=
    GetDot.eq.DotGet.fin _ V' i
  have hr : ([i < n] (((exp A'[i] * Ξ[i]) @ V') / id (α := Tensor ℝ* []) ((exp A'[i] * Ξ[i]).sum 0))).get i =
      (exp A'[i] * Ξ[i] / id (α := Tensor ℝ* []) ((exp A'[i] * Ξ[i]).sum 0)) @ V' :=
    (EqGetStack.fin (fun i : Fin n => ((exp A'[i] * Ξ[i]) @ V') / id (α := Tensor ℝ* []) ((exp A'[i] * Ξ[i]).sum 0)) i).trans
      (DotDiv.eq.DivDot (exp A'[i] * Ξ[i]) (id (α := Tensor ℝ* []) ((exp A'[i] * Ξ[i]).sum 0)) V').symm
  have hfin : ((A' + (Ξ - 1) * ∞).softmax.get ⟨i, by grind⟩) @ V' ≈ ((id (α := Tensor ℝ [n]) (exp A₀[i] * Ξ₀[i] / id (α := Tensor ℝ []) ((exp A₀[i] * Ξ₀[i]).sum 0)) : Tensor ℝ [n]) : Tensor ℝ* [n]) @ V' :=
    XEqDotS.of.XEq (X := V) hrow_i
  refine (Tensor.XEq.of.Eq hl).trans (hfin.trans (Tensor.XEq.of.Eq ?_))
  exact (hrow i ▸ hr).symm


-- created on 2021-01-02
