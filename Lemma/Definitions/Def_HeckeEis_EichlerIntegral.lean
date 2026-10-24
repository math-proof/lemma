import Mathlib
import Lemma.Definitions.Def_HeckeEis_BinaryFormRep
import Lemma.Definitions.Def_Gamma0CoeffCohomology

noncomputable section

namespace HeckeEis

open UpperHalfPlane MvPolynomial CongruenceSubgroup
open scoped MatrixGroups

section LinePow

variable (n : ℕ)

theorem isHomogeneous_line (τ : ℂ) : (C τ * X 0 + X 1 : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
  ((isHomogeneous_X ℂ 0).C_mul τ).add (isHomogeneous_X ℂ 1)

theorem isHomogeneous_linePow (τ : ℂ) : ((C τ * X 0 + X 1 : MvPolynomial (Fin 2) ℂ) ^ n).IsHomogeneous n := by
  simpa using (isHomogeneous_line τ).pow n

def linePow (τ : ℂ) : ↥(BinaryForm ℂ n) :=
  ⟨(C τ * X 0 + X 1) ^ n, (mem_homogeneousSubmodule n _).mpr (isHomogeneous_linePow n τ)⟩

@[simp] theorem coe_linePow (τ : ℂ) :
    ((linePow n τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) = (C τ * X 0 + X 1) ^ n := rfl

def jFactor (g : SL(2, ℤ)) (τ : ℍ) : ℂ := ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (τ : ℂ) + ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)

theorem jFactor_eq_denom (g : SL(2, ℤ)) (τ : ℍ) :
    jFactor g τ = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) (τ : ℂ) := by
  rw [jFactor, Matrix.SpecialLinearGroup.mapGL, MonoidHom.comp_apply,
    show (algebraMap ℤ ℝ) = Int.castRingHom ℝ from rfl, ModularGroup.denom_apply]

theorem jFactor_ne_zero (g : SL(2, ℤ)) (τ : ℍ) : jFactor g τ ≠ 0 := by
  rw [jFactor_eq_denom]
  exact denom_ne_zero _ τ

theorem coe_smul_mul_jFactor (g : SL(2, ℤ)) (τ : ℍ) :
    ((g • τ : ℍ) : ℂ) * jFactor g τ
      = ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (τ : ℂ) + ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) := by
  rw [coe_specialLinearGroup_apply]
  have hj := jFactor_ne_zero g τ
  simp only [jFactor, eq_intCast, Complex.ofReal_intCast] at hj ⊢
  rw [div_mul_cancel₀ _ hj]

theorem binarySubst_line (M : Matrix (Fin 2) (Fin 2) ℤ) (τ : ℂ) :
    binarySubst ℂ M (C τ * X 0 + X 1)
      = C ((M 0 0 : ℂ) * τ + (M 0 1 : ℂ)) * X 0 + C ((M 1 0 : ℂ) * τ + (M 1 1 : ℂ)) * X 1 := by
  simp only [map_add, map_mul, binarySubst_C, binarySubst_X, Fin.sum_univ_two, Fin.isValue]
  ring

theorem binaryFormRepSL_linePow (g : SL(2, ℤ)) (τ : ℍ) :
    binaryFormRepSL ℂ n g (linePow n (τ : ℂ)) = (jFactor g τ) ^ n • linePow n ((g • τ : ℍ) : ℂ) := by
  apply Subtype.ext
  rw [binaryFormRepSL_apply_coe, Submodule.coe_smul, coe_linePow, coe_linePow, map_pow, binarySubst_line,
    smul_eq_C_mul, map_pow, ← mul_pow]
  congr 1
  rw [mul_add, ← mul_assoc, ← map_mul, mul_comm (jFactor g τ), coe_smul_mul_jFactor]
  rfl

end LinePow

section Equivariant

variable {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V] [Module K V]

def IsEquivariantPrimitiveWith (ρ : Representation K Γ V) (F : ℍ → V) : Prop :=
  ∀ γ : Γ, ∃ c : V, ∀ τ : ℍ, F ((γ : SL(2, ℤ)) • τ) - ρ γ (F τ) = c

namespace IsEquivariantPrimitiveWith

variable {ρ : Representation K Γ V} {F : ℍ → V}

def cocycle (_hF : IsEquivariantPrimitiveWith ρ F) (γ : Γ) : V :=
  F ((γ : SL(2, ℤ)) • I) - ρ γ (F I)

theorem sub_eq_cocycle (hF : IsEquivariantPrimitiveWith ρ F) (γ : Γ) (τ : ℍ) :
    F ((γ : SL(2, ℤ)) • τ) - ρ γ (F τ) = hF.cocycle γ := by
  obtain ⟨c, hc⟩ := hF γ
  rw [cocycle, hc τ, hc I]

theorem apply_smul (hF : IsEquivariantPrimitiveWith ρ F) (γ : Γ) (τ : ℍ) :
    F ((γ : SL(2, ℤ)) • τ) = hF.cocycle γ + ρ γ (F τ) := by
  rw [← hF.sub_eq_cocycle γ τ, sub_add_cancel]

theorem cocycle_mem_coeffCocycles (hF : IsEquivariantPrimitiveWith ρ F) : hF.cocycle ∈ coeffCocycles ρ := by
  intro γ δ
  have h := hF.apply_smul (γ * δ) I
  rw [Subgroup.coe_mul, mul_smul, hF.apply_smul γ, hF.apply_smul δ, map_add, map_mul, Module.End.mul_apply] at h

  have := congrArg (fun v => v - ρ γ (ρ δ (F I))) h
  simp only [add_sub_cancel_right] at this
  rw [← this]
  abel

end IsEquivariantPrimitiveWith

end Equivariant

section EichlerIntegral

variable (n : ℕ)

def IsEichlerIntegral (f : ℍ → ℂ) (F : ℍ → ↥(BinaryForm ℂ n)) : Prop :=
  ∀ (d : Fin 2 →₀ ℕ) (τ : ℍ),
    HasDerivAt (fun z : ℂ => MvPolynomial.coeff d ((F (ofComplex z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))
      (f τ * MvPolynomial.coeff d ((linePow n (τ : ℂ) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) (τ : ℂ)

variable (N : ℕ)

open Classical in

def eichlerShimuraMap (f : ℍ → ℂ) :
    coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) :=
  if h : ∃ F : ℍ → ↥(BinaryForm ℂ n), IsEichlerIntegral n f F ∧
      ∃ hF : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) F,
        IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) hF.cocycle
  then coeffH1parMk _ ⟨h.choose_spec.2.choose.cocycle,
    ⟨h.choose_spec.2.choose.cocycle_mem_coeffCocycles, h.choose_spec.2.choose_spec⟩⟩
  else 0

theorem eichlerShimuraMap_def (f : ℍ → ℂ) {F : ℍ → ↥(BinaryForm ℂ n)}
    (hEI : IsEichlerIntegral n f F)
    (hF : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) F)
    (hpar : IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) hF.cocycle) :
    ∃ (F₀ : ℍ → ↥(BinaryForm ℂ n)) (_ : IsEichlerIntegral n f F₀)
      (h₀ : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) F₀)
      (hpar₀ : IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) h₀.cocycle),
      eichlerShimuraMap n N f = coeffH1parMk _ ⟨h₀.cocycle, ⟨h₀.cocycle_mem_coeffCocycles, hpar₀⟩⟩ := by
  classical
  have h : ∃ F : ℍ → ↥(BinaryForm ℂ n), IsEichlerIntegral n f F ∧
      ∃ hF : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) F,
        IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) hF.cocycle := ⟨F, hEI, hF, hpar⟩
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.choose, h.choose_spec.2.choose_spec, dif_pos h⟩

theorem eichlerShimuraMap_of_not_exists (f : ℍ → ℂ)
    (h : ¬ ∃ F : ℍ → ↥(BinaryForm ℂ n), IsEichlerIntegral n f F ∧
      ∃ hF : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) F,
        IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) hF.cocycle) :
    eichlerShimuraMap n N f = 0 := by
  classical
  exact dif_neg h

end EichlerIntegral

end HeckeEis

end
