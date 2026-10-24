import Mathlib

open Matrix

noncomputable section

namespace LocalGL2

section CommRing

variable {R : Type*} [CommRing R]

def cartanDiag (ϖ : R) (a b : ℕ) : Matrix (Fin 2) (Fin 2) R :=
  !![ϖ ^ a, 0; 0, ϖ ^ b]

theorem cartanDiag_zero_zero (ϖ : R) : cartanDiag ϖ 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cartanDiag]

theorem cartanDiag_det (ϖ : R) (a b : ℕ) : (cartanDiag ϖ a b).det = ϖ ^ (a + b) := by
  rw [cartanDiag, Matrix.det_fin_two_of, mul_zero, sub_zero, ← pow_add]

def CartanRel (g h : Matrix (Fin 2) (Fin 2) R) : Prop :=
  ∃ k₁ k₂ : (Matrix (Fin 2) (Fin 2) R)ˣ, g = k₁.val * h * k₂.val

theorem CartanRel.refl (g : Matrix (Fin 2) (Fin 2) R) : CartanRel g g :=
  ⟨1, 1, by simp⟩

private theorem unit_conj_cancel (k₁ k₂ : (Matrix (Fin 2) (Fin 2) R)ˣ)
    (h : Matrix (Fin 2) (Fin 2) R) :
    (k₁⁻¹).val * (k₁.val * h * k₂.val) * (k₂⁻¹).val = h := by
  rw [mul_assoc k₁.val h k₂.val, Units.inv_mul_cancel_left, Units.mul_inv_cancel_right]

theorem CartanRel.symm {g h : Matrix (Fin 2) (Fin 2) R} (hgh : CartanRel g h) :
    CartanRel h g := by
  obtain ⟨k₁, k₂, rfl⟩ := hgh
  exact ⟨k₁⁻¹, k₂⁻¹, (unit_conj_cancel k₁ k₂ h).symm⟩

theorem CartanRel.trans {g h l : Matrix (Fin 2) (Fin 2) R} (hgh : CartanRel g h)
    (hhl : CartanRel h l) : CartanRel g l := by
  obtain ⟨k₁, k₂, rfl⟩ := hgh
  obtain ⟨m₁, m₂, rfl⟩ := hhl
  exact ⟨k₁ * m₁, m₂ * k₂, by simp only [Units.val_mul, mul_assoc]⟩

theorem cartanRel_unit_mul_mul (k₁ k₂ : (Matrix (Fin 2) (Fin 2) R)ˣ)
    (g : Matrix (Fin 2) (Fin 2) R) : CartanRel (k₁.val * g * k₂.val) g :=
  ⟨k₁, k₂, rfl⟩

theorem CartanRel.det_associated {g h : Matrix (Fin 2) (Fin 2) R} (hgh : CartanRel g h) :
    Associated g.det h.det := by
  obtain ⟨k₁, k₂, rfl⟩ := hgh
  have h₁ : IsUnit (k₁.val.det) := (Matrix.isUnit_iff_isUnit_det _).mp k₁.isUnit
  have h₂ : IsUnit (k₂.val.det) := (Matrix.isUnit_iff_isUnit_det _).mp k₂.isUnit
  rw [Matrix.det_mul, Matrix.det_mul]
  exact (associated_mul_isUnit_left_iff h₂).mpr ((associated_isUnit_mul_left_iff h₁).mpr
    (Associated.refl h.det))

def entryIdeal (g : Matrix (Fin 2) (Fin 2) R) : Ideal R :=
  Ideal.span (Set.range fun p : Fin 2 × Fin 2 => g p.1 p.2)

theorem entry_mem_entryIdeal (g : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    g i j ∈ entryIdeal g :=
  Ideal.subset_span ⟨(i, j), rfl⟩

theorem entryIdeal_le_iff {g : Matrix (Fin 2) (Fin 2) R} {I : Ideal R} :
    entryIdeal g ≤ I ↔ ∀ i j, g i j ∈ I := by
  rw [entryIdeal, Ideal.span_le]
  constructor
  · intro h i j; exact h ⟨(i, j), rfl⟩
  · rintro h _ ⟨⟨i, j⟩, rfl⟩; exact h i j

theorem entryIdeal_mul_le_right (M N : Matrix (Fin 2) (Fin 2) R) :
    entryIdeal (M * N) ≤ entryIdeal N := by
  rw [entryIdeal_le_iff]; intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem (Ideal.mul_mem_left _ _ (entry_mem_entryIdeal N 0 j))
    (Ideal.mul_mem_left _ _ (entry_mem_entryIdeal N 1 j))

theorem entryIdeal_mul_le_left (M N : Matrix (Fin 2) (Fin 2) R) :
    entryIdeal (M * N) ≤ entryIdeal M := by
  rw [entryIdeal_le_iff]; intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem (Ideal.mul_mem_right _ _ (entry_mem_entryIdeal M i 0))
    (Ideal.mul_mem_right _ _ (entry_mem_entryIdeal M i 1))

theorem CartanRel.entryIdeal_eq {g h : Matrix (Fin 2) (Fin 2) R} (hgh : CartanRel g h) :
    entryIdeal g = entryIdeal h := by
  obtain ⟨k₁, k₂, rfl⟩ := hgh
  refine le_antisymm ((entryIdeal_mul_le_left _ _).trans (entryIdeal_mul_le_right _ _)) ?_
  conv_lhs => rw [← unit_conj_cancel k₁ k₂ h]
  exact (entryIdeal_mul_le_left _ _).trans (entryIdeal_mul_le_right _ _)

theorem entryIdeal_cartanDiag (ϖ : R) {a b : ℕ} (hab : a ≤ b) :
    entryIdeal (cartanDiag ϖ a b) = Ideal.span {ϖ ^ a} := by
  refine le_antisymm ?_ ?_
  · rw [entryIdeal_le_iff]
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact Ideal.subset_span rfl
    · simp [cartanDiag]
    · simp [cartanDiag]
    · show ϖ ^ b ∈ _
      exact Ideal.mem_span_singleton.mpr (pow_dvd_pow ϖ hab)
  · rw [Ideal.span_singleton_le_iff_mem]
    exact entry_mem_entryIdeal (cartanDiag ϖ a b) 0 0

noncomputable def swapUnit : (Matrix (Fin 2) (Fin 2) R)ˣ :=
  ((Matrix.isUnit_iff_isUnit_det (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R)).mpr
    (by simp [Matrix.det_fin_two_of])).unit

@[simp] theorem swapUnit_val :
    (swapUnit (R := R)).val = !![0, 1; 1, 0] :=
  IsUnit.unit_spec _

end CommRing

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem pow_irreducible_dvd_pow_iff {ϖ : R} (hϖ : Irreducible ϖ) {a b : ℕ} :
    ϖ ^ a ∣ ϖ ^ b ↔ a ≤ b := by
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hϖ.addVal_pow, hϖ.addVal_pow, Nat.cast_le]

theorem pow_irreducible_associated_iff {ϖ : R} (hϖ : Irreducible ϖ) {a b : ℕ} :
    Associated (ϖ ^ a) (ϖ ^ b) ↔ a = b := by
  constructor
  · intro h
    exact le_antisymm ((pow_irreducible_dvd_pow_iff hϖ).mp h.dvd)
      ((pow_irreducible_dvd_pow_iff hϖ).mp h.symm.dvd)
  · rintro rfl; rfl

end DVR

end LocalGL2

end
