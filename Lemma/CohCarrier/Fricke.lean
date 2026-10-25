import Def.CohCarrier_Level

set_option autoImplicit false

namespace CohCarrier

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

section FrickeMat

variable (N : ℕ)

def frickeMat (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) : SL(2, ℤ) :=
  ⟨!![A 1 1, -(A 1 0 / N); -(N * A 0 1), A 0 0], by
    rw [Matrix.det_fin_two_of]
    have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at hdet
    have hc : A 1 0 / N * N = A 1 0 := Int.ediv_mul_cancel h
    have hc' : A 1 0 / N * (N * A 0 1) = A 1 0 * A 0 1 := by rw [← mul_assoc, hc]
    rw [neg_mul_neg, hc']
    linear_combination hdet⟩

@[simp] theorem frickeMat_apply_00 (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) :
    (frickeMat N A h) 0 0 = A 1 1 := by simp [frickeMat]
@[simp] theorem frickeMat_apply_01 (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) :
    (frickeMat N A h) 0 1 = -(A 1 0 / N) := by simp [frickeMat]
@[simp] theorem frickeMat_apply_10 (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) :
    (frickeMat N A h) 1 0 = -(N * A 0 1) := by simp [frickeMat]
@[simp] theorem frickeMat_apply_11 (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) :
    (frickeMat N A h) 1 1 = A 0 0 := by simp [frickeMat]

theorem N_dvd_frickeMat_10 (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) :
    (N : ℤ) ∣ (frickeMat N A h) 1 0 := by
  rw [frickeMat_apply_10]
  exact (dvd_mul_right _ _).neg_right

theorem frickeMat_mul (A B : SL(2, ℤ)) (hA : (N : ℤ) ∣ A 1 0) (hB : (N : ℤ) ∣ B 1 0)
    (hAB : (N : ℤ) ∣ (A * B) 1 0) :
    frickeMat N (A * B) hAB = frickeMat N A hA * frickeMat N B hB := by
  have hmul : ∀ i j, (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := fun i j => by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hcA : A 1 0 / N * N = A 1 0 := Int.ediv_mul_cancel hA
  have e1 : A 1 0 / N * (N * B 0 1) = A 1 0 * B 0 1 := by rw [← mul_assoc, hcA]
  have e2 : (N : ℤ) * A 0 1 * (B 1 0 / N) = A 0 1 * B 1 0 := by
    rw [mul_comm (N : ℤ), mul_assoc, Int.mul_ediv_cancel' hB]
  have h01 : (A 1 0 * B 0 0 + A 1 1 * B 1 0) / N = A 1 0 / N * B 0 0 + A 1 1 * (B 1 0 / N) := by
    rw [Int.add_ediv_of_dvd_right (Dvd.dvd.mul_left hB _), Int.mul_ediv_assoc _ hB,
      mul_comm (A 1 0) (B 0 0), Int.mul_ediv_assoc _ hA, mul_comm (B 0 0)]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [frickeMat, Matrix.mul_apply, Fin.sum_univ_two, hmul, h01] <;> linarith [e1, e2]

theorem frickeMat_frickeMat [NeZero N] (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0)
    (h' : (N : ℤ) ∣ (frickeMat N A h) 1 0) :
    frickeMat N (frickeMat N A h) h' = A := by
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have e01 : (N : ℤ) * A 0 1 / N = A 0 1 := Int.mul_ediv_cancel_left _ hN
  fin_cases i <;> fin_cases j <;>
    simp [frickeMat, Int.neg_ediv_of_dvd, e01, Int.mul_ediv_cancel' h]

theorem trace_frickeMat (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) :
    ((frickeMat N A h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [frickeMat, add_comm]

theorem N_dvd_of_mem_Gamma0 {A : SL(2, ℤ)} (hA : A ∈ Gamma0 N) : (N : ℤ) ∣ A 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hA)

theorem frickeMat_mem_Gamma0 {A : SL(2, ℤ)} (hA : A ∈ Gamma0 N) :
    frickeMat N A (N_dvd_of_mem_Gamma0 N hA) ∈ Gamma0 N := by
  rw [Gamma0_mem, frickeMat_apply_10]
  push_cast
  simp

theorem gamma0Units_frickeMat (γ : Gamma0 N) :
    gamma0Units N ⟨frickeMat N (γ : SL(2, ℤ)) (N_dvd_of_mem_Gamma0 N γ.2), frickeMat_mem_Gamma0 N γ.2⟩ =
      (gamma0Units N γ)⁻¹ := by
  apply Units.ext
  simp [gamma0Units, Gamma0Map, frickeMat]

variable (H : Subgroup (ZMod N)ˣ)

theorem N_dvd_of_mem_GammaH (γ : ↥(GammaH N H)) : (N : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
  N_dvd_of_mem_Gamma0 N (mem_GammaH_iff.mp γ.2).1

theorem frickeMat_mem (γ : ↥(GammaH N H)) :
    frickeMat N (γ : SL(2, ℤ)) (N_dvd_of_mem_GammaH N H γ) ∈ GammaH N H := by
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp γ.2
  refine mem_GammaH_iff.mpr ⟨frickeMat_mem_Gamma0 N hγ0, ?_⟩
  rw [gamma0Units_frickeMat N ⟨(γ : SL(2, ℤ)), hγ0⟩]
  exact H.inv_mem hγH

end FrickeMat

section FrickeHom

variable (N : ℕ) (H : Subgroup (ZMod N)ˣ)

def frickeHom : ↥(GammaH N H) →* ↥(GammaH N H) where
  toFun γ := ⟨frickeMat N (γ : SL(2, ℤ)) (N_dvd_of_mem_GammaH N H γ), frickeMat_mem N H γ⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [frickeMat]
  map_mul' γ δ := Subtype.ext (frickeMat_mul N _ _ (N_dvd_of_mem_GammaH N H γ)
    (N_dvd_of_mem_GammaH N H δ) (N_dvd_of_mem_GammaH N H (γ * δ)))

@[simp] theorem coe_frickeHom (γ : ↥(GammaH N H)) :
    ((frickeHom N H γ : ↥(GammaH N H)) : SL(2, ℤ)) =
      frickeMat N (γ : SL(2, ℤ)) (N_dvd_of_mem_GammaH N H γ) := rfl

theorem frickeHom_frickeHom [NeZero N] (γ : ↥(GammaH N H)) :
    frickeHom N H (frickeHom N H γ) = γ :=
  Subtype.ext (frickeMat_frickeMat N (γ : SL(2, ℤ)) (N_dvd_of_mem_GammaH N H γ)
    (N_dvd_of_mem_GammaH N H (frickeHom N H γ)))

def frickeEquiv [NeZero N] : ↥(GammaH N H) ≃* ↥(GammaH N H) :=
  { frickeHom N H with
    invFun := frickeHom N H
    left_inv := frickeHom_frickeHom N H
    right_inv := frickeHom_frickeHom N H }

@[simp] theorem frickeEquiv_apply [NeZero N] (γ : ↥(GammaH N H)) :
    frickeEquiv N H γ = frickeHom N H γ := rfl

@[simp] theorem frickeEquiv_symm_apply [NeZero N] (γ : ↥(GammaH N H)) :
    (frickeEquiv N H).symm γ = frickeHom N H γ := rfl

theorem trace_coe_frickeHom (γ : ↥(GammaH N H)) :
    (((frickeHom N H γ : ↥(GammaH N H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [coe_frickeHom, trace_frickeMat]

end FrickeHom

section FrickeH1

variable (N : ℕ) (H : Subgroup (ZMod N)ˣ) (A : Type*) [AddCommGroup A]

def frickeH1 : H1 N H A →+ H1 N H A where
  toFun φ := φ.comp (MonoidHom.toAdditive (frickeHom N H))
  map_zero' := by ext; rfl
  map_add' := by intro φ ψ; ext; rfl

@[simp] theorem frickeH1_apply (φ : H1 N H A) (γ : ↥(GammaH N H)) :
    frickeH1 N H A φ (Additive.ofMul γ) = φ (Additive.ofMul (frickeHom N H γ)) := rfl

theorem frickeH1_eq_comp (φ : H1 N H A) :
    frickeH1 N H A φ = φ.comp (MonoidHom.toAdditive (frickeHom N H)) := rfl

theorem frickeH1_frickeH1 [NeZero N] (φ : H1 N H A) :
    frickeH1 N H A (frickeH1 N H A φ) = φ := by
  refine AddMonoidHom.ext fun x => ?_
  show φ (Additive.ofMul (frickeHom N H (frickeHom N H (Additive.toMul x)))) = φ x
  rw [frickeHom_frickeHom]
  rfl

def frickeH1L (R : Type*) [Semiring R] [Module R A] : H1 N H A →ₗ[R] H1 N H A where
  toFun := frickeH1 N H A
  map_add' := map_add _
  map_smul' := by intro r φ; ext; rfl

@[simp] theorem frickeH1L_apply (R : Type*) [Semiring R] [Module R A] (φ : H1 N H A) :
    frickeH1L N H A R φ = frickeH1 N H A φ := rfl

theorem comp_frickeH1 {B : Type*} [AddCommGroup B] (f : A →+ B) (φ : H1 N H A) :
    f.comp (frickeH1 N H A φ) = frickeH1 N H B (f.comp φ) := rfl

end FrickeH1

end CohCarrier
