import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Band
import sympy.Basic
import Lemma.Nat.LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0
import Lemma.Int.Lt_Add.et.EqEMod.et.All_Le.of.Eq_Max.Dvd.Gt_0
open Tensor
set_option maxHeartbeats 2000000


private lemma sc_ext {x y : ℝ} (h : x = y) : (x : Tensor ℝ []) = (y : Tensor ℝ []) := by rw [h]


@[path]
private lemma band_part_mask.dilated
  {n l u d d_z : ℕ}
  {β : Fin n → ℕ}
  {A : Fin n → Fin n → ℝ}
  {V : Fin n → Fin d_z → ℝ}
-- given
  (h_d : 0 < d)
  (h_dl : (d : ℤ) ∣ (l : ℤ) - 1)
  (h_β : ∀ i : Fin n, (β i : ℤ) = max ((i.val : ℤ) - l + 1) (((i.val : ℤ) - l + 1) % d))
  (h_l : 0 < l)
  (h_u : 0 < u)
  (i : Fin n) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u ∧ ((j.val : ℤ) - (i.val : ℤ)) % d = 0)))
  let A₀ : Tensor ℝ* [n, n] := ([i < n] [j < n] ((A i j : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
  let Vᵢ : Tensor ℝ [n, d_z] := [j < n] [t < d_z] ((V j t : ℝ) : Tensor ℝ [])
  ((A₀ + (Ξ - 1) * ∞).softmax.get ⟨i, by grind⟩) @ (Vᵢ : Tensor ℝ* [n, d_z]) ≈
    ((([t < d_z] ((∑ m : Fin ((min n (i.val + u) - β i + d - 1) / d), Real.exp (A i ⟨β i + m * d, by have := Nat.LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0 h_d m.2; omega⟩) / (∑ m' : Fin ((min n (i.val + u) - β i + d - 1) / d), Real.exp (A i ⟨β i + m' * d, by have := Nat.LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0 h_d m'.2; omega⟩)) * V ⟨β i + m * d, by have := Nat.LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0 h_d m.2; omega⟩ t : ℝ) : Tensor ℝ [])) : Tensor ℝ [d_z]) : Tensor ℝ* [d_z]) := by
-- proof
  intro Ξ A₀ Vᵢ
  obtain ⟨hb1, hb2, hb3⟩ := Int.Lt_Add.et.EqEMod.et.All_Le.of.Eq_Max.Dvd.Gt_0 h_d h_dl (h_β i)
  have h_main := DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Band.dilated h_l h_u h_d (fun i j => A i j) (fun i j t => V j t) i hb1 hb2 hb3
  exact h_main


@[path]
private lemma band_part_mask.dilated.bert
  {n l u d d_z : ℕ}
  {β : Fin n → ℕ}
  {Q K V : Fin n → Fin d_z → ℝ}
-- given
  (h_d : 0 < d)
  (h_dl : (d : ℤ) ∣ (l : ℤ) - 1)
  (h_β : ∀ i : Fin n, (β i : ℤ) = max ((i.val : ℤ) - l + 1) (((i.val : ℤ) - l + 1) % d))
  (h_l : 0 < l)
  (h_u : 0 < u)
  (i : Fin n) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u ∧ ((j.val : ℤ) - (i.val : ℤ)) % d = 0)))
  let A₀ : Tensor ℝ* [n, n] := ([i < n] [j < n] (((∑ s, Q i s * K j s) / √(d_z : ℝ) : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
  let Vᵢ : Tensor ℝ [n, d_z] := [j < n] [t < d_z] ((V j t : ℝ) : Tensor ℝ [])
  ((A₀ + (Ξ - 1) * ∞).softmax.get ⟨i, by grind⟩) @ (Vᵢ : Tensor ℝ* [n, d_z]) ≈
    ((([t < d_z] ((∑ m : Fin ((min n (i.val + u) - β i + d - 1) / d), Real.exp ((∑ s, Q i s * K ⟨β i + m * d, by have := Nat.LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0 h_d m.2; omega⟩ s) / √(d_z : ℝ)) / (∑ m' : Fin ((min n (i.val + u) - β i + d - 1) / d), Real.exp ((∑ s, Q i s * K ⟨β i + m' * d, by have := Nat.LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0 h_d m'.2; omega⟩ s) / √(d_z : ℝ))) * V ⟨β i + m * d, by have := Nat.LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0 h_d m.2; omega⟩ t : ℝ) : Tensor ℝ [])) : Tensor ℝ [d_z]) : Tensor ℝ* [d_z]) := by
-- proof
  intro Ξ A₀ Vᵢ
  obtain ⟨hb1, hb2, hb3⟩ := Int.Lt_Add.et.EqEMod.et.All_Le.of.Eq_Max.Dvd.Gt_0 h_d h_dl (h_β i)
  have h_main := DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Band.dilated h_l h_u h_d (fun i j => (∑ s, Q i s * K j s) / √(d_z : ℝ)) (fun i j t => V j t) i hb1 hb2 hb3
  exact h_main


-- created on 2026-09-27
