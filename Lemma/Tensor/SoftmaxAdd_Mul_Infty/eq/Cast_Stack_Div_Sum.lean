import Lemma.Tensor.SoftmaxAdd_Mul_Infty.eq.Stack_Div_Sum
import Lemma.Tensor.GetDiv.eq.DivGet
import Lemma.Tensor.Sum_0.eq.Sum_Get
import Lemma.Tensor.MapStack.eq.Stack_Map
import Lemma.Tensor.XEq.of.Eq
import Lemma.Tensor.MapExp.eq.ExpMap.of.All_EqUFnExp_ExpUFn
import Lemma.Tensor.MapMul.eq.MulMapS.of.All_Eq_Mul
import Lemma.Tensor.MapDiv.eq.DivMapS.of.All_Eq_Div
import Lemma.Tensor.SumMap.eq.MapSum.of.All_EqUFnAdd
open Tensor Hyperreal
set_option maxHeartbeats 500000


private lemma coe_scalar
-- given
  (b : Bool) :
-- imply
  ((b.toNat : ℕ) : Tensor ℝ* []) = ((b.toNat : ℕ) : Tensor ℝ []).map Hyperreal.ofReal := by
-- proof
  apply Eq.of.EqDataS
  cases b <;> rfl

private lemma coe_mask
  {n m : ℕ}
-- given
  (p : Fin n → Fin m → Bool) :
-- imply
  ([i < n] [j < m] (Bool.toNat (p i j)) : Tensor ℝ* [n, m]) = (([i < n] [j < m] (Bool.toNat (p i j)) : Tensor ℝ [n, m]) : Tensor ℝ* [n, m]) := by
-- proof
  rw [MapStack.eq.Stack_Map]
  congr 1
  funext i
  rw [MapStack.eq.Stack_Map]
  congr 1

private lemma row_cast
  {m : ℕ}
-- given
  (X Y : Tensor ℝ [m]) :
-- imply
  Exp.exp (X : Tensor ℝ* [m]) * (Y : Tensor ℝ* [m]) / id (α := Tensor ℝ* []) ((Exp.exp (X : Tensor ℝ* [m]) * (Y : Tensor ℝ* [m])).sum 0) =
    ((Exp.exp X * Y / id (α := Tensor ℝ []) ((Exp.exp X * Y).sum 0) : Tensor ℝ [m]) : Tensor ℝ* [m]) := by
-- proof
  have hmul : ∀ a b : ℝ, Hyperreal.ofReal (a * b) = Hyperreal.ofReal a * Hyperreal.ofReal b := fun a b => Hyperreal.coe_mul a b
  have hdiv : ∀ a b : ℝ, Hyperreal.ofReal (a / b) = Hyperreal.ofReal a / Hyperreal.ofReal b := fun a b => Hyperreal.coe_div a b
  have hadd : ∀ a b : ℝ, Hyperreal.ofReal (a + b) = Hyperreal.ofReal a + Hyperreal.ofReal b := fun a b => Hyperreal.coe_add a b
  have hexp := MapExp.eq.ExpMap.of.All_EqUFnExp_ExpUFn (f := Hyperreal.ofReal) (fun x => OfRealExp.eq.ExpOfReal x) X
  change _ = (Exp.exp X * Y / id (α := Tensor ℝ []) ((Exp.exp X * Y).sum 0)).map Hyperreal.ofReal
  rw [MapDiv.eq.DivMapS.of.All_Eq_Div.scalar hdiv]
  rw [MapMul.eq.MulMapS.of.All_Eq_Mul hmul]
  have hs : ((Exp.exp X * Y).sum 0).map Hyperreal.ofReal = (((Exp.exp X * Y).map Hyperreal.ofReal).sum 0) := (SumMap.eq.MapSum.of.All_EqUFnAdd hadd _ 0).symm
  simp only [id]
  erw [hs]
  erw [MapMul.eq.MulMapS.of.All_Eq_Mul hmul (Exp.exp X) Y, hexp]

/--
The hyperreal masked softmax of a real tensor is (infinitely close to) a *real* tensor:
the row-wise formula \( \frac{e^{A_i} \odot \Xi_i}{\sum_j e^{A_{ij}} \Xi_{ij}} \) computed over \(\mathbb{R}\) and then cast to \(\mathbb{R}^*\),
where \( \Xi_{ij} = [p(i, j)] \) and every row has an unmasked entry.
-/
@[path]
private lemma main
  {n m : ℕ}
  {p : Fin n → Fin m → Bool}
-- given
  (h_ne : ∀ i : Fin n, ∃ j : Fin m, p i j = true)
  (A : Tensor ℝ [n, m]) :
-- imply
  let Ξ : Tensor ℝ* [n, m] := [i < n] [j < m] (Bool.toNat (p i j))
  let A' : Tensor ℝ* [n, m] := A
  let Ξ₀ : Tensor ℝ [n, m] := [i < n] [j < m] (Bool.toNat (p i j))
  (A' + (Ξ - 1) * ∞).softmax ≈
    (([i < n] (Exp.exp A[i] * Ξ₀[i] / id (α := Tensor ℝ []) ((Exp.exp A[i] * Ξ₀[i]).sum 0)) : Tensor ℝ [n, m]) : Tensor ℝ* [n, m]) := by
-- proof
  intro Ξ A' Ξ₀
  have hmain : (A' + (Ξ - 1) * ∞).softmax ≈ [i < n] (Exp.exp A'[i] * Ξ[i] / id (α := Tensor ℝ* []) ((Exp.exp A'[i] * Ξ[i]).sum 0)) :=
    SoftmaxAdd_Mul_Infty.eq.Stack_Div_Sum h_ne A
  have hΞ : Ξ = (Ξ₀ : Tensor ℝ* [n, m]) := coe_mask _
  have hrow : ∀ i : Fin n, Exp.exp A'[i] * Ξ[i] / id (α := Tensor ℝ* []) ((Exp.exp A'[i] * Ξ[i]).sum 0) =
      ((id (α := Tensor ℝ [m]) (Exp.exp A[i] * Ξ₀[i] / id (α := Tensor ℝ []) ((Exp.exp A[i] * Ξ₀[i]).sum 0)) : Tensor ℝ [m]) : Tensor ℝ* [m]) := by
    intro i
    have h1 : A'[i] = ((id (α := Tensor ℝ [m]) A[i] : Tensor ℝ [m]) : Tensor ℝ* [m]) :=
      GetMap.eq.MapGet.fin A Hyperreal.ofReal ⟨i, by simp [Tensor.length]⟩
    have h2 : Ξ[i] = ((id (α := Tensor ℝ [m]) Ξ₀[i] : Tensor ℝ [m]) : Tensor ℝ* [m]) := by
      rw [hΞ]
      apply GetMap.eq.MapGet.fin Ξ₀ Hyperreal.ofReal ⟨i, by simp [Tensor.length]⟩
    rw [h1, h2]
    apply row_cast (id (α := Tensor ℝ [m]) A[i]) (id (α := Tensor ℝ [m]) Ξ₀[i])
  apply hmain.trans
  apply Tensor.XEq.of.Eq
  refine (congrArg (fun f => ([i < n] f i : Tensor ℝ* [n, m])) (funext hrow)).trans ?_
  symm
  apply MapStack.eq.Stack_Map (f := Hyperreal.ofReal) (fun i : Fin n => (id (α := Tensor ℝ [m]) (Exp.exp A[i] * Ξ₀[i] / id (α := Tensor ℝ []) ((Exp.exp A[i] * Ξ₀[i]).sum 0))))


-- created on 2026-10-01
-- updated on 2026-11-13
