import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_EqAddMul.of.Lt_Mul
import Lemma.Nat.DivMulS.eq.Div.of.Ne_0
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LeAddMul___Mul.of.Lt
import Lemma.Nat.Lt.of.Lt.Le
import Lemma.Nat.LtAddS.is.Lt
import Lemma.Nat.LtMod.of.Ne_0
import Lemma.Nat.Mod_Mul.eq.AddMul_Mod.of.Lt
import Lemma.Nat.Mul
import Lemma.Nat.Mul.ne.Zero.of.Ne_0.Ne_0
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul
import Lemma.Nat.MulMul.eq.Mul_Mul
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Mod_Mul.lt.MulDiv.of.Mod_Mul.lt.MulDiv.Lt_Mul.Lt |
| mpr | Nat.Mod_Mul.lt.MulDiv.of.Mod_Mul.lt.MulDiv.Lt_Mul.mpr |
-/
@[main]
private lemma main
  {n t K M D κ δ : ℕ}
-- given
  (h_i : i < δ)
  (h_t : t < K * n * M * D)
  (h_r : ((t / D * δ + i) * D + t % D) % (n * (M * D) * δ) < n * (M * D) / (κ * M * D) * (κ * M * D) * δ) :
-- imply
  t % (n * (M * D)) < n * (M * D) / (κ * M * D) * (κ * M * D) := by
-- proof
  rw [MulAdd.eq.AddMulS] at h_r
  rw [AddAdd.eq.Add_Add] at h_r
  rw [MulMul.comm] at h_r
  have h_D_0 : D ≠ 0 := by grind
  have h_M_0 : M ≠ 0 := by grind
  have h_MD_0 := Mul.ne.Zero.of.Ne_0.Ne_0 h_M_0 h_D_0
  conv_rhs at h_r => rw [MulMul.eq.Mul_Mul (a := κ)]
  conv_rhs at h_r => rw [DivMulS.eq.Div.of.Ne_0 h_MD_0]
  conv_rhs at h_r => rw [Mul_Mul.eq.MulMul]
  conv_rhs => rw [MulMul.eq.Mul_Mul (a := κ)]
  conv_rhs => rw [DivMulS.eq.Div.of.Ne_0 h_MD_0]
  conv_rhs => rw [Mul_Mul.eq.MulMul]
  have h_n := EqAddMulDiv n κ
  set qₙ := n / κ with h_qₙ
  set rₙ := n % κ with h_rₙ
  rw [← h_n] at h_t
  obtain ⟨q, r, h_qr⟩ := Any_EqAddMul.of.Lt_Mul h_t
  let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr.symm
  rw [← h_q_div, ← h_r_mod] at h_r
  have h_add_mul := AddMul.lt.Mul.of.Lt.Lt h_i (LtMod.of.Ne_0 h_D_0 t)
  rw [← h_r_mod] at h_add_mul
  rw [← h_qr]
  rw [MulMul.eq.Mul_Mul] at h_r
  rw [Mul.comm (a := δ)] at h_add_mul
  rw [Mul_Mul.eq.MulMul (a := n)] at h_r
  rw [MulMul.eq.Mul_Mul (b := D)] at h_r
  rw [Mod_Mul.eq.AddMul_Mod.of.Lt (by grind)] at h_r
  rw [Mul_Mul.eq.MulMul] at h_r ⊢
  rw [Mod_Mul.eq.AddMul_Mod.of.Lt (by grind)]
  have h_r_mod : r < D := by grind
  apply Lt.of.Lt.Le (LtAddS.of.Lt.left (↑q % (n * M) * D) h_r_mod)
  have h_mod_lt : q % (n * M) < qₙ * κ * M := by
    apply Nat.lt_of_mul_lt_mul_right _ (a := D)
    conv_rhs => rw [MulMul.eq.Mul_Mul]
    apply Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h_r)
  apply le_trans (LeAddMul___Mul.of.Lt h_mod_lt D) (by grind)


/--
| attributes | lemma |
| :---: | :---: |
| mpr | Nat.Mod_Mul.lt.MulDiv.of.Mod_Mul.lt.MulDiv.Lt_Mul.mpr |
-/
@[main]
private lemma mpr
  {n t K M D κ δ : ℕ}
-- given
  (h_div : n % κ = 0)
  (h_i : i < δ)
  (h_t : t < K * n * M * D)
  (h_c : t % (n * (M * D)) < n * (M * D) / (κ * M * D) * (κ * M * D)) :
-- imply
  ((t / D * δ + i) * D + t % D) % (n * (M * D) * δ) < n * (M * D) / (κ * M * D) * (κ * M * D) * δ := by
-- proof
  rw [MulAdd.eq.AddMulS]
  rw [AddAdd.eq.Add_Add]
  rw [MulMul.comm]
  have h_D_0 : D ≠ 0 := by grind
  have h_M_0 : M ≠ 0 := by grind
  have h_MD_0 := Mul.ne.Zero.of.Ne_0.Ne_0 h_M_0 h_D_0
  conv_rhs at h_c => rw [MulMul.eq.Mul_Mul (a := κ)]
  conv_rhs at h_c => rw [DivMulS.eq.Div.of.Ne_0 h_MD_0]
  conv_rhs at h_c => rw [Mul_Mul.eq.MulMul]
  conv_rhs => rw [MulMul.eq.Mul_Mul (a := κ)]
  conv_rhs => rw [DivMulS.eq.Div.of.Ne_0 h_MD_0]
  conv_rhs => rw [Mul_Mul.eq.MulMul]
  have h_n := EqAddMulDiv n κ
  set qₙ := n / κ with h_qₙ
  set rₙ := n % κ with h_rₙ
  rw [h_div] at h_rₙ h_n
  simp [h_rₙ] at h_n
  rw [← h_n] at h_t
  obtain ⟨q, r, h_qr⟩ := Any_EqAddMul.of.Lt_Mul h_t
  let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr.symm
  rw [← h_q_div, ← h_r_mod]
  rw [← h_qr] at h_c
  conv at h_c =>
    lhs
    arg 2
    rw [← Nat.mul_assoc]
  rw [Mod_Mul.eq.AddMul_Mod.of.Lt (by grind)] at h_c
  have h_add_mul := AddMul.lt.Mul.of.Lt.Lt h_i (LtMod.of.Ne_0 h_D_0 t)
  rw [← h_r_mod] at h_add_mul
  rw [MulMul.eq.Mul_Mul]
  rw [Mul.comm (a := δ)] at h_add_mul
  rw [Mul_Mul.eq.MulMul (a := n)]
  rw [MulMul.eq.Mul_Mul (b := D)]
  rw [Mod_Mul.eq.AddMul_Mod.of.Lt (by grind)]
  rw [Mul_Mul.eq.MulMul]
  have h_r_lt : ↑r < D := by grind
  have h_mod_lt : ↑q % (n * M) < qₙ * κ * M := by
    apply Nat.lt_of_mul_lt_mul_right _ (a := D)
    conv_rhs => rw [MulMul.eq.Mul_Mul]
    exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h_c
  have h_qδ : (↑q % (n * M)) * δ + i < qₙ * κ * M * δ := by
    have h_δ_pos : 0 < δ := Nat.pos_of_ne_zero (by grind : δ ≠ 0)
    have h_succ := Nat.succ_le_iff.mpr h_mod_lt
    have h_mul_le : (↑q % (n * M)).succ * δ ≤ qₙ * κ * M * δ :=
      Nat.mul_le_mul h_succ (Nat.le_refl δ)
    have h_bound : (↑q % (n * M)) * δ + δ ≤ qₙ * κ * M * δ := by
      simpa [Nat.succ_eq_add_one, Nat.mul_add, Nat.add_mul, Nat.mul_one] using h_mul_le
    have h_i_le : i ≤ δ - 1 := by
      match δ, h_i with
      | 0, _ => exfalso; grind
      | δ' + 1, h_i' => simpa using Nat.lt_succ_iff.mpr h_i'
    have h_step : (↑q % (n * M)) * δ + i < (↑q % (n * M)) * δ + δ :=
      Nat.add_lt_add_left (Nat.lt_of_le_of_lt h_i_le (Nat.pred_lt_self h_δ_pos)) _
    exact Nat.lt_of_lt_of_le h_step h_bound
  have h_goal_eq :
      (↑q % (n * M) * D) * δ + (i * D + ↑r) = D * ((↑q % (n * M)) * δ + i) + ↑r := by
    ring_nf
  rw [h_goal_eq]
  have h_rhs : D * (qₙ * κ * M * δ) = qₙ * κ * (M * D) * δ := by ring
  have h_le : D * ((↑q % (n * M)) * δ + i) + D ≤ D * (qₙ * κ * M * δ) := by
    have h_succ : ((↑q % (n * M)) * δ + i) + 1 ≤ qₙ * κ * M * δ := Nat.succ_le_iff.mpr h_qδ
    calc
      D * ((↑q % (n * M)) * δ + i) + D
          = D * (((↑q % (n * M)) * δ + i) + 1) := by ring
      _ ≤ D * (qₙ * κ * M * δ) := Nat.mul_le_mul_left D h_succ
  rw [← h_rhs]
  exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left h_r_lt _) h_le


-- created on 2026-08-04
