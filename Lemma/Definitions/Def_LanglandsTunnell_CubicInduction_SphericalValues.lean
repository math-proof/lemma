import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.CubicInduction.SphericalValues

variable (e₁ e₂ e₃ : ℂ)

def completeHom (n : ℕ) : ℂ := sphericalTorusValue e₁ e₂ e₃ n

theorem completeHom_eq (n : ℕ) : completeHom e₁ e₂ e₃ n = sphericalTorusValue e₁ e₂ e₃ n := rfl

theorem completeHom_zero : completeHom e₁ e₂ e₃ 0 = 1 := rfl

theorem completeHom_one : completeHom e₁ e₂ e₃ 1 = e₁ := rfl

theorem completeHom_two : completeHom e₁ e₂ e₃ 2 = e₁ ^ 2 - e₂ := rfl

def completeHomPred : ℕ → ℂ
  | 0 => 0
  | n + 1 => completeHom e₁ e₂ e₃ n

theorem completeHomPred_zero : completeHomPred e₁ e₂ e₃ 0 = 0 := rfl

theorem completeHomPred_one : completeHomPred e₁ e₂ e₃ 1 = 1 := rfl

theorem completeHomPred_succ (n : ℕ) :
    completeHomPred e₁ e₂ e₃ (n + 1) = completeHom e₁ e₂ e₃ n := rfl

theorem completeHom_add_two (n : ℕ) :
    completeHom e₁ e₂ e₃ (n + 2) =
      e₁ * completeHom e₁ e₂ e₃ (n + 1) - e₂ * completeHom e₁ e₂ e₃ n +
        e₃ * completeHomPred e₁ e₂ e₃ n := by
  cases n with
  | zero =>
    show sphericalTorusValue e₁ e₂ e₃ 2 =
      e₁ * sphericalTorusValue e₁ e₂ e₃ 1 - e₂ * sphericalTorusValue e₁ e₂ e₃ 0 + e₃ * 0
    simp only [sphericalTorusValue]
    ring
  | succ k =>
    show sphericalTorusValue e₁ e₂ e₃ (k + 3) =
      e₁ * sphericalTorusValue e₁ e₂ e₃ (k + 2) - e₂ * sphericalTorusValue e₁ e₂ e₃ (k + 1) +
        e₃ * sphericalTorusValue e₁ e₂ e₃ k
    simp only [sphericalTorusValue]

def schurTwoRow (m₁ : ℕ) : ℕ → ℂ
  | 0 => completeHom e₁ e₂ e₃ m₁
  | k + 1 =>
    completeHom e₁ e₂ e₃ m₁ * completeHom e₁ e₂ e₃ (k + 1) -
      completeHom e₁ e₂ e₃ (m₁ + 1) * completeHom e₁ e₂ e₃ k

theorem schurTwoRow_eq (m₁ m₂ : ℕ) :
    schurTwoRow e₁ e₂ e₃ m₁ m₂ =
      completeHom e₁ e₂ e₃ m₁ * completeHom e₁ e₂ e₃ m₂ -
        completeHom e₁ e₂ e₃ (m₁ + 1) * completeHomPred e₁ e₂ e₃ m₂ := by
  cases m₂ with
  | zero => simp [schurTwoRow, completeHomPred_zero, completeHom_zero]
  | succ k => rfl

abbrev IsDominant (a b c : ℤ) : Prop := b ≤ a ∧ c ≤ b

def sphericalValue (q : ℂ) (a b c : ℤ) : ℂ :=
  if IsDominant a b c then
    e₃ ^ c * q⁻¹ ^ (a - c).toNat * schurTwoRow e₁ e₂ e₃ (a - c).toNat (b - c).toNat
  else 0

theorem sphericalValue_of_isDominant (q : ℂ) (a b c : ℤ) (hd : IsDominant a b c) :
    sphericalValue e₁ e₂ e₃ q a b c =
      e₃ ^ c * q⁻¹ ^ (a - c).toNat * schurTwoRow e₁ e₂ e₃ (a - c).toNat (b - c).toNat := by
  rw [sphericalValue, if_pos hd]

theorem sphericalValue_of_not_isDominant (q : ℂ) (a b c : ℤ) (hd : ¬ IsDominant a b c) :
    sphericalValue e₁ e₂ e₃ q a b c = 0 := by
  rw [sphericalValue, if_neg hd]

section Identities

variable {q : ℂ} (hq : q ≠ 0) (he₃ : e₃ ≠ 0)
include hq he₃

theorem pieri_first {a b c : ℤ} (hba : b ≤ a) (hcb : c ≤ b) :
    q ^ 2 * sphericalValue e₁ e₂ e₃ q (a + 1) b c + q * sphericalValue e₁ e₂ e₃ q a (b + 1) c +
        sphericalValue e₁ e₂ e₃ q a b (c + 1) =
      q * e₁ * sphericalValue e₁ e₂ e₃ q a b c := by
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hcb)
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hba)
  have hz : e₃ ^ (c + 1) = e₃ ^ c * e₃ := zpow_add_one₀ he₃ c
  have hqp : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
  rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a + 1) (b) (c) ⟨by omega, by omega⟩]
  rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a) (b) (c) ⟨by omega, by omega⟩]
  cases m with
  | zero =>
    have hn3 : ¬ IsDominant (a) (b) (c + 1) := fun hd => by
      have h1 := hd.1
      have h2 := hd.2
      omega
    rw [sphericalValue_of_not_isDominant e₁ e₂ e₃ q (a) (b) (c + 1) hn3]
    cases j with
    | zero =>
      have hn2 : ¬ IsDominant (a) (b + 1) (c) := fun hd => by
        have h1 := hd.1
        have h2 := hd.2
        omega
      rw [sphericalValue_of_not_isDominant e₁ e₂ e₃ q (a) (b + 1) (c) hn2]
      have t1 : (a + 1 - c).toNat = 1 := by omega
      have t2 : (b - c).toNat = 0 := by omega
      have t3 : (a - c).toNat = 0 := by omega
      rw [t1, t2, t3]
      simp only [schurTwoRow_eq, completeHomPred_zero, completeHom_zero, completeHom_one]
      field_simp
      ring
    | succ i =>
      rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a) (b + 1) (c) ⟨by omega, by omega⟩]
      have t1 : (a + 1 - c).toNat = i + 1 + 1 := by omega
      have t2 : (b - c).toNat = 0 := by omega
      have t3 : (a - c).toNat = i + 1 := by omega
      have t4 : (b + 1 - c).toNat = 1 := by omega
      rw [t1, t2, t3, t4]
      simp only [schurTwoRow_eq, completeHomPred_zero, completeHomPred_one, completeHom_zero,
        completeHom_one]
      linear_combination
        (e₃ ^ c * q⁻¹ ^ i * completeHom e₁ e₂ e₃ (i + 1 + 1) * q⁻¹ * q) * hqp
  | succ k =>
    rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a) (b) (c + 1) ⟨by omega, by omega⟩]
    cases j with
    | zero =>
      have hn2 : ¬ IsDominant (a) (b + 1) (c) := fun hd => by
        have h1 := hd.1
        have h2 := hd.2
        omega
      rw [sphericalValue_of_not_isDominant e₁ e₂ e₃ q (a) (b + 1) (c) hn2]
      have t1 : (a + 1 - c).toNat = k + 1 + 1 := by omega
      have t2 : (b - c).toNat = k + 1 := by omega
      have t3 : (a - c).toNat = k + 1 := by omega
      have t4 : (a - (c + 1)).toNat = k := by omega
      have t5 : (b - (c + 1)).toNat = k := by omega
      rw [t1, t2, t3, t4, t5, hz]
      simp only [schurTwoRow_eq, completeHomPred_succ]
      have r1 : completeHom e₁ e₂ e₃ (k + 1 + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + 1 + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k + 1) +
              e₃ * completeHomPred e₁ e₂ e₃ (k + 1) :=
        completeHom_add_two e₁ e₂ e₃ (k + 1)
      have r2 : completeHom e₁ e₂ e₃ (k + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k) +
              e₃ * completeHomPred e₁ e₂ e₃ (k) :=
        completeHom_add_two e₁ e₂ e₃ (k)
      rw [completeHomPred_succ] at r1
      rw [r1, r2]
      linear_combination
        (-(e₃ ^ c * q⁻¹ ^ k *
            (e₁ ^ 2 * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + 1) * q⁻¹ * q
              - e₁ * e₂ * completeHom e₁ e₂ e₃ k ^ 2 * q⁻¹ * q
              + e₁ * e₃ * completeHom e₁ e₂ e₃ k * completeHomPred e₁ e₂ e₃ k * q⁻¹ * q
              - e₁ * completeHom e₁ e₂ e₃ (k + 1) ^ 2 * q⁻¹ * q
              + e₃ * completeHom e₁ e₂ e₃ k ^ 2 * q⁻¹ * q + e₃ * completeHom e₁ e₂ e₃ k ^ 2
              - e₃ * completeHom e₁ e₂ e₃ (k + 1) * completeHomPred e₁ e₂ e₃ k * q⁻¹ * q
              - e₃ * completeHom e₁ e₂ e₃ (k + 1) * completeHomPred e₁ e₂ e₃ k))) * hqp
    | succ i =>
      rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a) (b + 1) (c) ⟨by omega, by omega⟩]
      have t1 : (a + 1 - c).toNat = k + i + 1 + 1 + 1 := by omega
      have t2 : (b - c).toNat = k + 1 := by omega
      have t3 : (a - c).toNat = k + i + 1 + 1 := by omega
      have t4 : (b + 1 - c).toNat = k + 1 + 1 := by omega
      have t5 : (a - (c + 1)).toNat = k + i + 1 := by omega
      have t6 : (b - (c + 1)).toNat = k := by omega
      rw [t1, t2, t3, t4, t5, t6, hz]
      simp only [schurTwoRow_eq, completeHomPred_succ]
      have r1 : completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k + i + 1 + 1) +
              e₃ * completeHomPred e₁ e₂ e₃ (k + i + 1 + 1) :=
        completeHom_add_two e₁ e₂ e₃ (k + i + 1 + 1)
      have r2 : completeHom e₁ e₂ e₃ (k + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k) +
              e₃ * completeHomPred e₁ e₂ e₃ (k) :=
        completeHom_add_two e₁ e₂ e₃ (k)
      rw [completeHomPred_succ] at r1
      rw [r1, r2]
      linear_combination
        (-(e₃ ^ c * q⁻¹ ^ (k + i) * q⁻¹ *
            (e₁ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1) * q⁻¹ * q
              - e₂ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + i + 1 + 1) * q⁻¹ * q
              + e₃ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + i + 1) * q⁻¹ * q
              + e₃ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + i + 1)
              - e₃ * completeHom e₁ e₂ e₃ (k + i + 1 + 1) * completeHomPred e₁ e₂ e₃ k
              - completeHom e₁ e₂ e₃ (k + 1) * completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1) * q⁻¹ * q))) * hqp

theorem pieri_second {a b c : ℤ} (hba : b ≤ a) (hcb : c ≤ b) :
    q ^ 2 * sphericalValue e₁ e₂ e₃ q (a + 1) (b + 1) c + q * sphericalValue e₁ e₂ e₃ q (a + 1) b (c + 1) +
        sphericalValue e₁ e₂ e₃ q a (b + 1) (c + 1) =
      q * e₂ * sphericalValue e₁ e₂ e₃ q a b c := by
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hcb)
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hba)
  have hz : e₃ ^ (c + 1) = e₃ ^ c * e₃ := zpow_add_one₀ he₃ c
  have hqp : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
  rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a + 1) (b + 1) (c) ⟨by omega, by omega⟩]
  rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a) (b) (c) ⟨by omega, by omega⟩]
  cases m with
  | zero =>
    have hn2 : ¬ IsDominant (a + 1) (b) (c + 1) := fun hd => by
      have h1 := hd.1
      have h2 := hd.2
      omega
    rw [sphericalValue_of_not_isDominant e₁ e₂ e₃ q (a + 1) (b) (c + 1) hn2]
    cases j with
    | zero =>
      have hn3 : ¬ IsDominant (a) (b + 1) (c + 1) := fun hd => by
        have h1 := hd.1
        have h2 := hd.2
        omega
      rw [sphericalValue_of_not_isDominant e₁ e₂ e₃ q (a) (b + 1) (c + 1) hn3]
      have t1 : (a + 1 - c).toNat = 1 := by omega
      have t2 : (b + 1 - c).toNat = 1 := by omega
      have t3 : (a - c).toNat = 0 := by omega
      have t4 : (b - c).toNat = 0 := by omega
      have h11 : completeHom e₁ e₂ e₃ (1 + 1) = e₁ ^ 2 - e₂ := completeHom_two e₁ e₂ e₃
      rw [t1, t2, t3, t4]
      simp only [schurTwoRow_eq, completeHomPred_zero, completeHomPred_one, completeHom_zero,
        completeHom_one, h11]
      field_simp
      ring
    | succ i =>
      rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a) (b + 1) (c + 1) ⟨by omega, by omega⟩]
      have t1 : (a + 1 - c).toNat = i + 1 + 1 := by omega
      have t2 : (b + 1 - c).toNat = 1 := by omega
      have t3 : (a - c).toNat = i + 1 := by omega
      have t4 : (b - c).toNat = 0 := by omega
      have t5 : (a - (c + 1)).toNat = i := by omega
      have t6 : (b + 1 - (c + 1)).toNat = 0 := by omega
      rw [t1, t2, t3, t4, t5, t6, hz]
      simp only [schurTwoRow_eq, completeHomPred_zero, completeHomPred_one, completeHom_zero,
        completeHom_one]
      have r1 : completeHom e₁ e₂ e₃ (i + 1 + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (i + 1 + 1) -
            e₂ * completeHom e₁ e₂ e₃ (i + 1) +
              e₃ * completeHomPred e₁ e₂ e₃ (i + 1) :=
        completeHom_add_two e₁ e₂ e₃ (i + 1)
      rw [completeHomPred_succ] at r1
      rw [r1]
      linear_combination
        (e₃ ^ c * q⁻¹ ^ i *
            (e₂ * completeHom e₁ e₂ e₃ (i + 1) * q⁻¹ * q - e₃ * completeHom e₁ e₂ e₃ i * q⁻¹ * q
              - e₃ * completeHom e₁ e₂ e₃ i)) * hqp
  | succ k =>
    rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a + 1) (b) (c + 1) ⟨by omega, by omega⟩]
    cases j with
    | zero =>
      have hn3 : ¬ IsDominant (a) (b + 1) (c + 1) := fun hd => by
        have h1 := hd.1
        have h2 := hd.2
        omega
      rw [sphericalValue_of_not_isDominant e₁ e₂ e₃ q (a) (b + 1) (c + 1) hn3]
      have t1 : (a + 1 - c).toNat = k + 1 + 1 := by omega
      have t2 : (b + 1 - c).toNat = k + 1 + 1 := by omega
      have t3 : (a + 1 - (c + 1)).toNat = k + 1 := by omega
      have t4 : (b - (c + 1)).toNat = k := by omega
      have t5 : (a - c).toNat = k + 1 := by omega
      have t6 : (b - c).toNat = k + 1 := by omega
      rw [t1, t2, t3, t4, t5, t6, hz]
      simp only [schurTwoRow_eq, completeHomPred_succ]
      have r1 : completeHom e₁ e₂ e₃ (k + 1 + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + 1 + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k + 1) +
              e₃ * completeHomPred e₁ e₂ e₃ (k + 1) :=
        completeHom_add_two e₁ e₂ e₃ (k + 1)
      have r2 : completeHom e₁ e₂ e₃ (k + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k) +
              e₃ * completeHomPred e₁ e₂ e₃ (k) :=
        completeHom_add_two e₁ e₂ e₃ (k)
      rw [completeHomPred_succ] at r1
      rw [r1, r2]
      linear_combination
        (-(e₃ ^ c * q⁻¹ ^ k * q⁻¹ * q *
            (e₁ * e₂ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + 1)
              - e₁ * e₃ * completeHom e₁ e₂ e₃ (k + 1) * completeHomPred e₁ e₂ e₃ k
              - e₂ ^ 2 * completeHom e₁ e₂ e₃ k ^ 2 + 2 * e₂ * e₃ * completeHom e₁ e₂ e₃ k * completeHomPred e₁ e₂ e₃ k
              - e₂ * completeHom e₁ e₂ e₃ (k + 1) ^ 2 - e₃ ^ 2 * completeHomPred e₁ e₂ e₃ k ^ 2
              + e₃ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + 1)))) * hqp
    | succ i =>
      rw [sphericalValue_of_isDominant e₁ e₂ e₃ q (a) (b + 1) (c + 1) ⟨by omega, by omega⟩]
      have t1 : (a + 1 - c).toNat = k + i + 1 + 1 + 1 := by omega
      have t2 : (b + 1 - c).toNat = k + 1 + 1 := by omega
      have t3 : (a + 1 - (c + 1)).toNat = k + i + 1 + 1 := by omega
      have t4 : (b - (c + 1)).toNat = k := by omega
      have t5 : (a - (c + 1)).toNat = k + i + 1 := by omega
      have t6 : (b + 1 - (c + 1)).toNat = k + 1 := by omega
      have t7 : (a - c).toNat = k + i + 1 + 1 := by omega
      have t8 : (b - c).toNat = k + 1 := by omega
      rw [t1, t2, t3, t4, t5, t6, t7, t8, hz]
      simp only [schurTwoRow_eq, completeHomPred_succ]
      have r1 : completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k + i + 1 + 1) +
              e₃ * completeHomPred e₁ e₂ e₃ (k + i + 1 + 1) :=
        completeHom_add_two e₁ e₂ e₃ (k + i + 1 + 1)
      have r2 : completeHom e₁ e₂ e₃ (k + 1 + 1) =
          e₁ * completeHom e₁ e₂ e₃ (k + 1) -
            e₂ * completeHom e₁ e₂ e₃ (k) +
              e₃ * completeHomPred e₁ e₂ e₃ (k) :=
        completeHom_add_two e₁ e₂ e₃ (k)
      rw [completeHomPred_succ] at r1
      rw [r1, r2]
      linear_combination
        (-(e₃ ^ c * q⁻¹ ^ (k + i) * q⁻¹ *
            (e₂ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1) * q⁻¹ * q
              - e₂ * completeHom e₁ e₂ e₃ (k + 1) * completeHom e₁ e₂ e₃ (k + i + 1 + 1) * q⁻¹ * q
              - e₃ * completeHom e₁ e₂ e₃ k * completeHom e₁ e₂ e₃ (k + i + 1 + 1)
              + e₃ * completeHom e₁ e₂ e₃ (k + 1) * completeHom e₁ e₂ e₃ (k + i + 1) * q⁻¹ * q
              + e₃ * completeHom e₁ e₂ e₃ (k + 1) * completeHom e₁ e₂ e₃ (k + i + 1)
              - e₃ * completeHom e₁ e₂ e₃ (k + i + 1 + 1 + 1) * completeHomPred e₁ e₂ e₃ k * q⁻¹ * q))) * hqp

end Identities

example {q : ℂ} (hq : q ≠ 0) (he₃ : e₃ ≠ 0) :
    q ^ 2 * sphericalValue e₁ e₂ e₃ q 1 1 0 + q * sphericalValue e₁ e₂ e₃ q 1 0 1 + sphericalValue e₁ e₂ e₃ q 0 1 1 =
      q * e₂ * sphericalValue e₁ e₂ e₃ q 0 0 0 := by
  simpa using pieri_second e₁ e₂ e₃ hq he₃ (le_refl (0 : ℤ)) (le_refl (0 : ℤ))

example {q : ℂ} (hq : q ≠ 0) (he₃ : e₃ ≠ 0) :
    q ^ 2 * sphericalValue e₁ e₂ e₃ q 2 0 0 + q * sphericalValue e₁ e₂ e₃ q 1 1 0 + sphericalValue e₁ e₂ e₃ q 1 0 1 =
      q * e₁ * sphericalValue e₁ e₂ e₃ q 1 0 0 := by
  simpa using pieri_first e₁ e₂ e₃ hq he₃ (zero_le_one' ℤ) (le_refl (0 : ℤ))

section TorusPoints

variable (q : ℂ)

theorem sphericalValue_natCast_zero_zero (n : ℕ) :
    sphericalValue e₁ e₂ e₃ q n 0 0 = q⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n := by
  rw [sphericalValue_of_isDominant e₁ e₂ e₃ q n 0 0 ⟨by exact_mod_cast Nat.zero_le n, le_refl 0⟩]
  have h1 : ((n : ℤ) - 0).toNat = n := by omega
  have h2 : ((0 : ℤ) - 0).toNat = 0 := by omega
  rw [h1, h2, zpow_zero, one_mul]
  simp [schurTwoRow, completeHom]

theorem sphericalValue_natCast_succ_zero (k₁ k₂ : ℕ) (h : k₂ + 1 ≤ k₁) :
    sphericalValue e₁ e₂ e₃ q k₁ (k₂ + 1) 0 =
      q⁻¹ ^ k₁ * (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
        sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂) := by
  rw [sphericalValue_of_isDominant e₁ e₂ e₃ q k₁ (k₂ + 1) 0 ⟨by exact_mod_cast h, by positivity⟩]
  have h1 : ((k₁ : ℤ) - 0).toNat = k₁ := by omega
  have h2 : ((k₂ : ℤ) + 1 - 0).toNat = k₂ + 1 := by omega
  rw [h1, h2, zpow_zero, one_mul]
  simp [schurTwoRow, completeHom]

end TorusPoints

section Controls

example :
    (2 : ℂ) ^ 2 * sphericalValue (7 / 2) (7 / 2) 1 2 2 0 0 + 2 * sphericalValue (7 / 2) (7 / 2) 1 2 1 1 0 +
        sphericalValue (7 / 2) (7 / 2) 1 2 1 0 1 =
      2 * (7 / 2) * sphericalValue (7 / 2) (7 / 2) 1 2 1 0 0 := by
  rw [sphericalValue_of_isDominant _ _ _ _ 2 0 0 ⟨by norm_num, le_refl 0⟩,
    sphericalValue_of_isDominant _ _ _ _ 1 1 0 ⟨le_refl 1, by norm_num⟩,
    sphericalValue_of_not_isDominant _ _ _ _ 1 0 1 (by rintro ⟨-, h⟩; norm_num at h),
    sphericalValue_of_isDominant _ _ _ _ 1 0 0 ⟨by norm_num, le_refl 0⟩]
  simp only [show ((2 : ℤ) - 0).toNat = 2 by decide, show ((1 : ℤ) - 0).toNat = 1 by decide,
    show ((0 : ℤ) - 0).toNat = 0 by decide]
  norm_num [schurTwoRow, completeHom, completeHomPred, sphericalTorusValue]

example :
    (2 : ℂ) * sphericalValue (7 / 2) (7 / 2) 1 2 2 0 0 + 2 ^ 2 * sphericalValue (7 / 2) (7 / 2) 1 2 1 1 0 +
        sphericalValue (7 / 2) (7 / 2) 1 2 1 0 1 ≠
      2 * (7 / 2) * sphericalValue (7 / 2) (7 / 2) 1 2 1 0 0 := by
  rw [sphericalValue_of_isDominant _ _ _ _ 2 0 0 ⟨by norm_num, le_refl 0⟩,
    sphericalValue_of_isDominant _ _ _ _ 1 1 0 ⟨le_refl 1, by norm_num⟩,
    sphericalValue_of_not_isDominant _ _ _ _ 1 0 1 (by rintro ⟨-, h⟩; norm_num at h),
    sphericalValue_of_isDominant _ _ _ _ 1 0 0 ⟨by norm_num, le_refl 0⟩]
  simp only [show ((2 : ℤ) - 0).toNat = 2 by decide, show ((1 : ℤ) - 0).toNat = 1 by decide,
    show ((0 : ℤ) - 0).toNat = 0 by decide]
  norm_num [schurTwoRow, completeHom, completeHomPred, sphericalTorusValue]

example {q : ℂ} (hq : q ≠ 0) (he₃ : e₃ ≠ 0) :
    q ^ 2 * sphericalValue e₁ e₂ e₃ q 3 1 0 + q * sphericalValue e₁ e₂ e₃ q 3 0 1 +
        sphericalValue e₁ e₂ e₃ q 2 1 1 =
      q * e₂ * sphericalValue e₁ e₂ e₃ q 2 0 0 := by
  simpa using pieri_second e₁ e₂ e₃ hq he₃ (show (0 : ℤ) ≤ 2 by norm_num) (le_refl (0 : ℤ))

end Controls

end LanglandsTunnell.CubicInduction.SphericalValues

end

#print axioms LanglandsTunnell.CubicInduction.SphericalValues.pieri_first
#print axioms LanglandsTunnell.CubicInduction.SphericalValues.pieri_second
#print axioms LanglandsTunnell.CubicInduction.SphericalValues.sphericalValue_natCast_zero_zero
#print axioms LanglandsTunnell.CubicInduction.SphericalValues.sphericalValue_natCast_succ_zero
#check @LanglandsTunnell.CubicInduction.SphericalValues.sphericalValue
#check @LanglandsTunnell.CubicInduction.SphericalValues.schurTwoRow
#check @LanglandsTunnell.CubicInduction.SphericalValues.pieri_first
#check @LanglandsTunnell.CubicInduction.SphericalValues.pieri_second
