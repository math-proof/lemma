import Lemma.Tensor.SoftmaxAdd_Mul_Infty.eq.Stack_Div_Sum
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

/--
The hyperreal masked softmax of a real tensor is (infinitely close to) a *real* tensor:
the row-wise formula \( \frac{e^{A_i} \odot \Xi_i}{\sum_j e^{A_{ij}} \Xi_{ij}} \) computed over \(\mathbb{R}\) and then cast to \(\mathbb{R}^*\),
where \( \Xi_{ij} = [p(i, j)] \) and every row has an unmasked entry.
-/
@[path]
private lemma main
  {n m : ℕ}
-- given
  (p : Fin n → Fin m → Bool)
  (A : Tensor ℝ [n, m])
  (h_ne : ∀ i : Fin n, ∃ j : Fin m, p i j = true) :
-- imply
  let Ξ : Tensor ℝ* [n, m] := [i < n] [j < m] (Bool.toNat (p i j))
  let A' : Tensor ℝ* [n, m] := A
  let Ξ₀ : Tensor ℝ [n, m] := [i < n] [j < m] (Bool.toNat (p i j))
  (A' + (Ξ - 1) * ∞).softmax ≈
    (([i < n] (exp A[i] * Ξ₀[i] / id (α := Tensor ℝ []) ((exp A[i] * Ξ₀[i]).sum 0)) : Tensor ℝ [n, m]) : Tensor ℝ* [n, m]) := by
-- proof
  intro Ξ A' Ξ₀
  have hmain : (A' + (Ξ - 1) * ∞).softmax ≈ [i < n] (exp A'[i] * Ξ[i] / id (α := Tensor ℝ* []) ((exp A'[i] * Ξ[i]).sum 0)) :=
    SoftmaxAdd_Mul_Infty.eq.Stack_Div_Sum p A h_ne
  have hΞ : Ξ = (Ξ₀ : Tensor ℝ* [n, m]) := coe_mask _
  have hrow : ∀ i : Fin n, exp A'[i] * Ξ[i] / id (α := Tensor ℝ* []) ((exp A'[i] * Ξ[i]).sum 0) =
      ((id (α := Tensor ℝ [m]) (exp A[i] * Ξ₀[i] / id (α := Tensor ℝ []) ((exp A[i] * Ξ₀[i]).sum 0)) : Tensor ℝ [m]) : Tensor ℝ* [m]) := by
    intro i
    have h1 : A'[i] = ((id (α := Tensor ℝ [m]) A[i] : Tensor ℝ [m]) : Tensor ℝ* [m]) :=
      GetMap.eq.MapGet.fin A Hyperreal.ofReal ⟨i, by simp [Tensor.length]⟩
    have h2 : Ξ[i] = ((id (α := Tensor ℝ [m]) Ξ₀[i] : Tensor ℝ [m]) : Tensor ℝ* [m]) := by
      rw [hΞ]
      exact GetMap.eq.MapGet.fin Ξ₀ Hyperreal.ofReal ⟨i, by simp [Tensor.length]⟩
    rw [h1, h2]
    exact row_cast (id (α := Tensor ℝ [m]) A[i]) (id (α := Tensor ℝ [m]) Ξ₀[i])
  have hB : ([i < n] (exp A'[i] * Ξ[i] / id (α := Tensor ℝ* []) ((exp A'[i] * Ξ[i]).sum 0))) =
      ((([i < n] (id (α := Tensor ℝ [m]) (exp A[i] * Ξ₀[i] / id (α := Tensor ℝ []) ((exp A[i] * Ξ₀[i]).sum 0)))) : Tensor ℝ [n, m]) : Tensor ℝ* [n, m]) := by
    refine (congrArg (fun f => ([i < n] f i : Tensor ℝ* [n, m])) (funext hrow)).trans ?_
    symm
    exact MapStack.eq.Stack_Map (f := Hyperreal.ofReal) (fun i : Fin n => (id (α := Tensor ℝ [m]) (exp A[i] * Ξ₀[i] / id (α := Tensor ℝ []) ((exp A[i] * Ξ₀[i]).sum 0))))
  exact hmain.trans (Tensor.XEq.of.Eq hB)


-- created on 2026-10-01
