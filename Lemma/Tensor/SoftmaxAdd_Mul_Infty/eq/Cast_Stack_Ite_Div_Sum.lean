import Lemma.Tensor.SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Div_Sum
open Tensor Hyperreal
set_option maxHeartbeats 500000


private lemma sum_sc
  {m : ℕ}
-- given
  (h : Fin m → ℝ) :
-- imply
  ((∑ k, h k : ℝ) : Tensor ℝ []) = ∑ k, ((h k : ℝ) : Tensor ℝ []) := by
-- proof
  let φ : ℝ →+ Tensor ℝ [] := AddMonoidHom.mk' (fun x => (x : Tensor ℝ [])) (fun x y => by apply Eq.of.EqDataS; rfl)
  apply map_sum φ h Finset.univ

private lemma sc_ext
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  (x : Tensor ℝ []) = (y : Tensor ℝ []) := by
-- proof
  rw [h]

private lemma real_row
  {m : ℕ}
-- given
  (f g : Fin m → ℝ) :
-- imply
  let X : Tensor ℝ [m] := [j < m] (f j : Tensor ℝ [])
  let Y : Tensor ℝ [m] := [j < m] (g j : Tensor ℝ [])
  Exp.exp X * Y / id (α := Tensor ℝ []) ((Exp.exp X * Y).sum 0) =
    ([j < m] ((Real.exp (f j) * g j / ∑ k, Real.exp (f k) * g k : ℝ) : Tensor ℝ [])) := by
-- proof
  intro X Y
  apply Eq.of.All_EqGetS.fin
  intro j
  have hd := GetDiv.eq.DivGet.fin (Exp.exp X * Y) (((Exp.exp X * Y).sum 0 : Tensor ℝ [])) j
  have hs := Sum_0.eq.Sum_Get.fin (Exp.exp X * Y)
  have hm := fun i => GetMul.eq.MulGetS.fin (Exp.exp X) Y i
  have he := fun i => GetExp.eq.ExpGet.fin X i
  have hX : ∀ i : Fin m, X.get i = (f i : Tensor ℝ []) := fun i => EqGetStack.fin (fun j => (f j : Tensor ℝ [])) i
  have hY : ∀ i : Fin m, Y.get i = (g i : Tensor ℝ []) := fun i => EqGetStack.fin (fun j => (g j : Tensor ℝ [])) i
  have hterm : ∀ i : Fin m, (Exp.exp X * Y).get i = ((Real.exp (f i) * g i : ℝ) : Tensor ℝ []) := by
    intro i
    rw [hm i]
    erw [he i]
    rw [hX i, hY i]
    rfl
  have hsum : ((Exp.exp X * Y).sum 0 : Tensor ℝ []) = ((∑ k, (Real.exp (f k) * g k) : ℝ) : Tensor ℝ []) := by
    rw [hs]
    simp only [hterm]
    apply Eq.symm (sum_sc _)
  simp only [id]
  erw [hd, hterm j, hsum]
  erw [EqGetStack.fin (fun j => ((Real.exp (f j) * g j / ∑ k, Real.exp (f k) * g k : ℝ) : Tensor ℝ [])) j]
  rfl

private lemma sc_bool
-- given
  (b : Bool) :
-- imply
  ((b.toNat : ℕ) : Tensor ℝ []) = (((b.toNat : ℕ) : ℝ) : Tensor ℝ []) := by
-- proof
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
@[path]
private lemma main
  {n m : ℕ}
  {p : Fin n → Fin m → Bool}
-- given
  (h_ne : ∀ i : Fin n, ∃ j : Fin m, p i j = true)
  (a : Fin n → Fin m → ℝ) :
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
    (([i < n] (Exp.exp A₀[i] * Ξ₀[i] / id (α := Tensor ℝ []) ((Exp.exp A₀[i] * Ξ₀[i]).sum 0)) : Tensor ℝ [n, m]) : Tensor ℝ* [n, m]) :=
    SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Div_Sum h_ne A₀
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
-- updated on 2026-11-13
