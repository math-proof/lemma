import Mathlib
import Lemma.Gamma0CoeffCohomology.Main
import Lemma.HeckeEis.BinaryFormRep
import Instance.Gamma0CoeffCohomologyEigen
import Def.Gamma0CoeffCohomologyEigen

set_option autoImplicit false

namespace HeckeEis

open CongruenceSubgroup
open scoped MatrixGroups

section H1

variable {G : Type*} [Group G] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]


theorem coeffH1Mk_surjective (ρ : Representation K G V) : Function.Surjective (coeffH1Mk ρ) :=
  Submodule.mkQ_surjective _

theorem coeffH1Mk_eq_zero_iff (ρ : Representation K G V) (z : ↥(coeffCocycles ρ)) :
    coeffH1Mk ρ z = 0 ↔ (z : G → V) ∈ coeffCoboundaries ρ :=
  (Submodule.Quotient.mk_eq_zero _).trans Submodule.mem_comap

end H1

section Parabolic

variable {Γ : Subgroup SL(2, ℤ)} {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]


theorem coeffH1parToH1_coeffH1parMk (ρ : Representation K Γ V) (z : ↥(coeffParabolicCocycles ρ)) :
    coeffH1parToH1 ρ (coeffH1parMk ρ z) =
      coeffH1Mk ρ (Submodule.inclusion (coeffParabolicCocycles_le_coeffCocycles ρ) z) :=
  rfl

end Parabolic


section BinaryFormRep

variable (K : Type*) [CommRing K] (n : ℕ)


@[simp]
theorem binaryFormRep_apply_coe (M : Matrix (Fin 2) (Fin 2) ℤ) (F : ↥(BinaryForm K n)) :
    ((binaryFormRep K n M F : ↥(BinaryForm K n)) : MvPolynomial (Fin 2) K) = binarySubst K M F :=
  rfl

theorem binaryFormRepSL_apply_eq_binaryFormRep (g : SL(2, ℤ)) :
    binaryFormRepSL K n g = binaryFormRep K n (g : Matrix (Fin 2) (Fin 2) ℤ) :=
  rfl

theorem binaryFormAlphaAdj_eq_binaryFormRep (ℓ : ℕ) :
    binaryFormAlphaAdj K n ℓ = binaryFormRep K n !![(ℓ : ℤ), 0; 0, 1] :=
  rfl

end BinaryFormRep

end HeckeEis
