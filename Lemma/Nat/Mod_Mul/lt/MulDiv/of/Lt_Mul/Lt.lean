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


@[main]
private lemma main
  {n t K M D κ δ : ℕ}
-- given
  (h_i : i < δ)
  (h_t : t < K * n * M * D) :
-- imply
  ((t / D * δ + i) * D + t % D) % (n * (M * D) * δ) < n * (M * D) / (κ * M * D) * (κ * M * D) * δ ↔
  t % (n * (M * D)) < n * (M * D) / (κ * M * D) * (κ * M * D) := by
  rw [MulAdd.eq.AddMulS]
  rw [AddAdd.eq.Add_Add]
  rw [MulMul.comm]
  have h_D_0 : D ≠ 0 := by grind
  have h_M_0 : M ≠ 0 := by grind
  have h_MD_0 := Mul.ne.Zero.of.Ne_0.Ne_0 h_M_0 h_D_0
  rw [MulMul.eq.Mul_Mul (a := κ)]
  rw [DivMulS.eq.Div.of.Ne_0 h_MD_0]
  rw [Mul_Mul.eq.MulMul (b := κ)]
  have h_n := EqAddMulDiv n κ
  set qₙ := n / κ with h_qₙ
  set rₙ := n % κ with h_rₙ
  simp [h_rₙ] at h_n
  rw [← h_n] at h_t
  obtain ⟨q, r, h_qr⟩ := Any_EqAddMul.of.Lt_Mul h_t
  let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr.symm
  rw [← h_q_div, ← h_r_mod]
  have h_add_mul := AddMul.lt.Mul.of.Lt.Lt h_i (LtMod.of.Ne_0 h_D_0 t)
  rw [← h_r_mod] at h_add_mul
  rw [Mul.comm (a := δ)] at h_add_mul
  rw [← h_qr]
  rw [MulMul.eq.Mul_Mul]
  rw [Mul_Mul.eq.MulMul (a := n)]
  rw [MulMul.eq.Mul_Mul (b := D)]
  rw [Mod_Mul.eq.AddMul_Mod.of.Lt (by grind)]
  rw [Mod_Mul.eq.AddMul_Mod.of.Lt (by grind)]
  rw [Mul_Mul.eq.MulMul]
  have h_r_mod : r < D := by grind
  constructor
  ·
    intro h_r
    apply Lt.of.Lt.Le (LtAddS.of.Lt.left (↑q % (n * M) * D) h_r_mod)
    have h_mod_lt : q % (n * M) < qₙ * κ * M := by
      apply Nat.lt_of_mul_lt_mul_right _ (a := D)
      conv_rhs => rw [MulMul.eq.Mul_Mul]
      apply Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h_r)
    apply le_trans (LeAddMul___Mul.of.Lt h_mod_lt D) (by grind)
  ·
    intro h_c
    have h_mod_lt : ↑q % (n * M) < qₙ * κ * M := by
      apply Nat.lt_of_mul_lt_mul_right _ (a := D)
      conv_rhs => rw [MulMul.eq.Mul_Mul]
      exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h_c
    have h_goal_eq : (↑q % (n * M) * D) * δ + (i * D + ↑r) = D * ((↑q % (n * M)) * δ + i) + ↑r := by ring_nf
    rw [h_goal_eq]
    have h_rhs : D * (qₙ * κ * M * δ) = qₙ * κ * (M * D) * δ := by ring
    rw [← h_rhs]
    refine Nat.lt_of_lt_of_le (Nat.add_lt_add_left h_r_mod _) ?_
    calc
      _ = D * (((↑q % (n * M)) * δ + i) + 1) := by ring
      _ ≤ D * (qₙ * κ * M * δ) := by
        refine Nat.mul_le_mul_left D (Nat.succ_le_iff.mpr ?_)
        apply Nat.lt_of_lt_of_le
        .
          refine Nat.add_lt_add_left (Nat.lt_of_le_of_lt ?_ (Nat.pred_lt_self (Nat.pos_of_ne_zero (by grind : δ ≠ 0)))) _
          match δ, h_i with
          | 0, _ => exfalso; grind
          | δ' + 1, h_i' => simpa using Nat.lt_succ_iff.mpr h_i'
        .
          simpa [Nat.succ_eq_add_one, Nat.mul_add, Nat.add_mul, Nat.mul_one] using Nat.mul_le_mul (Nat.succ_le_iff.mpr h_mod_lt) (Nat.le_refl δ)


-- created on 2026-08-04
