import Lemma.Tensor.Div_KeepdimSum.eq.Div_Sum
import Lemma.Tensor.Ge_0.is.All_Le0GetData
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.ExpAdd_MulInfty.eq.Mul_Stack_Bool.rect
import Lemma.Tensor.Get.of.Eq
import Lemma.Tensor.GeExp_0
import Lemma.Tensor.GetDiv.eq.DivGetS
import Lemma.Tensor.GetKeepdim.eq.KeepdimCast_Get.of.GtGet_0.Gt_0.GtLength
import Lemma.Tensor.GetSum.as.SumGet.of.GtGet_0.LtAdd_1Length
import Lemma.Tensor.Le0Get.of.Ge_0
import Lemma.Tensor.Le0Mul.of.Ge_0.Ge_0
import Lemma.Tensor.Le0Stack.of.All_Ge_0
import Lemma.Tensor.Softmax.eq.DivExp_KeepdimSumExp
import Lemma.Tensor.XEqDivS_Sum_0.of.XEq.NotInfinitesimalSum.Ge_0
import Lemma.Tensor.XEqGetS.of.XEq.GtLength
import Lemma.Hyperreal.OfRealExp.eq.ExpOfReal
import Def.Data.Tensor.Sum
open Tensor Hyperreal
set_option maxHeartbeats 800000


private lemma ge_zero_mask
  {n m : ℕ}
-- given
  (p : Fin n → Fin m → Bool) :
-- imply
  let Ξ : Tensor ℝ* [n, m] := [i < n] [j < m] (Bool.toNat (p i j))
  Ξ ≥ 0 := by
-- proof
  intro Ξ
  apply Le0Stack.of.All_Ge_0
  intro i'
  apply Le0Stack.of.All_Ge_0
  intro j'
  refine ge_iff_le.mpr ?_
  apply Le.of.LeDataS
  intro k
  have hzero : ((0 : Tensor ℝ* []).data)[k] = (0 : ℝ*) := by
    rw [EqData0'0]
    apply Vector.EqGet0_0.fin (α := ℝ*) k
  fin_cases k
  rw [hzero]
  cases p i' j'
  ·
    change (0 : ℝ*) ≤ ((0 : ℕ) : ℝ*)
    apply Nat.cast_nonneg 0
  ·
    change (0 : ℝ*) ≤ ((1 : ℕ) : ℝ*)
    apply Nat.cast_nonneg 1

private lemma not_infinitesimal_sum
  {m : ℕ}
  {x : List.Vector ℝ* m}
  {j : Fin m}
  {δ : ℝ}
-- given
  (hx : ∀ k : Fin m, (0 : ℝ*) ≤ x[k])
  (hδ : 0 < δ)
  (hj : Hyperreal.ofReal δ ≤ x[j]) :
-- imply
  ¬(x.sum → 0) := by
-- proof
  intro h
  rw [Infinitesimal.is.All_LtAbs] at h
  have h1 := h ⟨δ, hδ⟩
  have h2 : x[j] ≤ x.sum := by
    rw [Vector.Sum.eq.Sum_Get]
    exact Finset.single_le_sum (f := fun k : Fin m => x[k]) (fun k _ => hx k) (Finset.mem_univ j)
  have h3 : (0 : ℝ*) ≤ x.sum := le_trans (hx j) h2
  rw [abs_of_nonneg h3] at h1
  have : Hyperreal.ofReal δ ≤ x.sum := le_trans hj h2
  apply absurd h1 (not_lt.mpr this)

private lemma lower_bound
  {n m : ℕ}
  {p : Fin n → Fin m → Bool}
  {i : Fin n}
  {j : Fin m}
-- given
  (hi : (i : ℕ) < n)
  (hjd : p i j = true)
  (A : Tensor ℝ [n, m]) :
-- imply
  let Ξ : Tensor ℝ* [n, m] := [i < n] [j < m] (Bool.toNat (p i j))
  let A' : Tensor ℝ* [n, m] := A
  Hyperreal.ofReal (Real.exp ((A[i] : Tensor ℝ [m]).data.get (Fin.cast (by simp) j))) ≤
    (((Exp.exp A').get ⟨i, hi⟩ * Ξ.get ⟨i, hi⟩ : Tensor ℝ* [m]).data.get (Fin.cast (by simp) j)) := by
-- proof
  intro Ξ A'
  have hexp : (Exp.exp A').get ⟨i, hi⟩ = Exp.exp (A'.get ⟨i, hi⟩) := GetExp.eq.ExpGet.fin A' ⟨i, hi⟩
  have h2 : (A'.get ⟨i, hi⟩ : Tensor ℝ* [m]) = (A[i] : Tensor ℝ [m]).map Hyperreal.ofReal := by
    simp [GetElem.getElem, A']
    erw [GetMap.eq.MapGet.fin]
    rfl
  have hmul := Vector.GetMul.eq.MulGetS.fin ((Exp.exp A').get ⟨i, hi⟩).data (Ξ.get ⟨i, hi⟩).data (Fin.cast (by simp) j)
  have e1 : ((Exp.exp A').get ⟨i, hi⟩).data.get (Fin.cast (by simp) j) = Hyperreal.ofReal (Real.exp ((A[i] : Tensor ℝ [m]).data.get (Fin.cast (by simp) j))) := by
    rw [hexp, h2]
    erw [DataExp.eq.ExpData]
    erw [Vector.GetExp.eq.ExpGet.fin]
    simp only [Tensor.map, GetElem.getElem, List.Vector.get_map]
    exact (OfRealExp.eq.ExpOfReal _).symm
  have e2 : (Ξ.get ⟨i, hi⟩).data.get (Fin.cast (by simp) j) = 1 := by
    have := GetData.eq.GetDataGet.of.Lt.fin (α := ℝ*) (n := m) (i := j) j.isLt (Ξ.get ⟨i, hi⟩)
    simp at this
    refine this.trans ?_
    have hb : p i j = true := hjd
    have hrow : (Ξ.get ⟨i, hi⟩ : Tensor ℝ* [m]) = [j < m] (Bool.toNat (p i j)) := by
      simp only [Ξ]
      erw [EqGetStack.fin]
      rfl
    rw [hrow]
    erw [EqGetStack.fin]
    refine (show ∀ (b : Bool) (_ : b = true), ((b.toNat : ℕ) : Tensor ℝ* []).data[0] = 1 from ?_) _ hb
    intro b hb'
    subst hb'
    change ((1 : ℕ) : Tensor ℝ* []).data[0] = 1
    refine ((Vector.Get_0.eq.Head.fin _).trans (EqHeadData.nat (α := ℝ*) 1)).trans ?_
    apply Nat.cast_one
  show _ ≤ (((Exp.exp A').get ⟨i, hi⟩).data * (Ξ.get ⟨i, hi⟩).data).get (Fin.cast (by simp) j)
  rw [hmul, e1, e2]
  simp

/--
Generic hyperreal masked softmax (py: `softmax(A + (Ξ - 1) * oo)` for a 0/1 mask `Ξ`), row by row:
\[
\operatorname{softmax}\left(A + (\Xi - 1) \cdot \infty\right) \approx
\left[ \frac{e^{A_i} \cdot \Xi_i}{\sum_j e^{A_{ij}} \Xi_{ij}} \right]_{i < n},
\qquad \Xi_{ij} = [p_{ij}].
\]
The only hypothesis is `h_ne` (every row has an unmasked entry), needed for the denominator to be non-infinitesimal.
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
  let A : Tensor ℝ* [n, m] := A
  (A + (Ξ - 1) * ∞).softmax ≈ [i < n] Exp.exp A[i] * Ξ[i] / id (α := Tensor ℝ* []) ((Exp.exp A[i] * Ξ[i]).sum 0) := by
-- proof
  intro Ξ A'
  have h_Ξ : Exp.exp (A' + (Ξ - 1) * ∞) ≈ Exp.exp A' * Ξ :=
    ExpAdd_MulInfty.eq.Mul_Stack_Bool.rect p A
  denote h_a' : a' = (A' + (Ξ - 1) * ∞)
  rw [← h_a'] at h_Ξ ⊢
  denote h_z : z = a'.softmax
  rw [← h_z]
  apply @Tensor.XEq.of.All_XEqGetS.fin
  intro i
  have hi : (i : ℕ) < n := i.isLt
  have h_Ξᵢ := XEqGetS.of.XEq.GtLength.fin (i := i) (by grind) h_Ξ
  simp at h_Ξᵢ
  have hmuld : (Exp.exp A' * Ξ).get ⟨↑i, by grind⟩ = (Exp.exp A').get ⟨↑i, hi⟩ * Ξ.get ⟨↑i, hi⟩ := by
    convert GetMul.eq.MulGetS.fin (Exp.exp A') Ξ ⟨↑i, hi⟩ <;> rfl
  rw [hmuld] at h_Ξᵢ
  have h_zi := Get.of.Eq.fin h_z i
  simp at h_zi
  rw [Softmax.eq.DivExp_KeepdimSumExp] at h_zi
  conv_rhs at h_zi => erw [@Tensor.GetDiv.eq.DivGetS.fin]
  simp at h_zi
  erw [GetKeepdim.eq.KeepdimCast_Get.of.GtGet_0.Gt_0.GtLength (i := i) (by grind) (by grind) (by grind) ((Exp.exp a').sum 1)] at h_zi
  erw [GetSum.eq.Cast_SumGet.of.GtGet_0.LtAdd_1Length.fin (d := 0) (by grind) (by grind)] at h_zi
  simp at h_zi
  erw [Div_KeepdimSum.eq.Div_Sum] at h_zi
  have hΞ0 : Ξ ≥ 0 := ge_zero_mask p
  have hexp : (Exp.exp A').get ⟨i, hi⟩ = Exp.exp (A'.get ⟨i, hi⟩) :=
    GetExp.eq.ExpGet.fin A' ⟨i, hi⟩
  have h_pos : (Exp.exp A').get ⟨i, hi⟩ * Ξ.get ⟨i, hi⟩ ≥ 0 := by
    apply Le0Mul.of.Ge_0.Ge_0
    ·
      rw [hexp]
      exact GeExp_0 _
    ·
      exact Le0Get.of.Ge_0 hΞ0 ⟨i, hi⟩
  have h_not : ¬(((Exp.exp A').get ⟨i, hi⟩ * Ξ.get ⟨i, hi⟩ : Tensor ℝ* [m]).data.sum → 0) := by
    obtain ⟨j, hj⟩ := h_ne i
    apply not_infinitesimal_sum
      (j := Fin.cast (by simp) j)
      (δ := Real.exp ((A[i] : Tensor ℝ [m]).data.get (Fin.cast (by simp) j)))
      (fun k => All_Le0GetData.of.Ge_0 h_pos k)
      (Real.exp_pos _)
      (lower_bound hi hj A)
  have h_fin := XEqDivS_Sum_0.of.XEq.NotInfinitesimalSum.Ge_0 h_pos h_not (y := (Exp.exp a').get i) h_Ξᵢ
  conv_rhs => erw [EqGetStack.fin]
  rw [h_zi]
  rwa [hexp] at h_fin


-- created on 2026-10-01
-- updated on 2026-11-13
