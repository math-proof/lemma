import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma exists_kernelField {G : Type*} [Group G] [Finite G]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (hM : FiniteDimensional ℚ M)
    (hker : M.fixingSubgroup ≤ ρ.ker) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      F.fixingSubgroup = ρ.ker ∧ Module.finrank ℚ F ∣ Nat.card G := by
  classical
  let hnorm : Normal ℚ (AlgebraicClosure ℚ) := by
    have h : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  let hsep : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) :=
    ⟨fun x => (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)).separable⟩
  let _ : IsGalois ℚ (AlgebraicClosure ℚ) := IsGalois.mk
  let _ := hM
  have hopen : IsOpen ((ρ.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    Subgroup.isOpen_mono hker M.fixingSubgroup_isOpen
  have hclosed : IsClosed ((ρ.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    Subgroup.isClosed_of_isOpen _ hopen
  let H : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := ⟨ρ.ker, hclosed⟩
  set F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField ρ.ker with hFdef
  have hfix : F.fixingSubgroup = ρ.ker := InfiniteGalois.fixingSubgroup_fixedField H
  have hfg : FiniteDimensional ℚ F ∧ IsGalois ℚ F := (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois F).mp
    ⟨by show IsOpen (F.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)); rw [hfix]; exact hopen,
     by rw [hfix]; exact MonoidHom.normal_ker ρ⟩
  let _ : FiniteDimensional ℚ F := hfg.1
  let _ : IsGalois ℚ F := hfg.2
  refine ⟨F, hfg.1, hfg.2, hfix, ?_⟩
  have hk : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker = ρ.ker :=
    (IntermediateField.restrictNormalHom_ker F).trans hfix
  have h1 : Nat.card (F ≃ₐ[ℚ] F) = Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ ρ.ker) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (AlgEquiv.restrictNormalHom_surjective (F := ℚ) (E := AlgebraicClosure ℚ) (K₁ := F))).toEquiv]
    exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hk).toEquiv
  have h2 : Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ ρ.ker) = Nat.card ρ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
  rw [← IsGalois.card_aut_eq_finrank, h1, h2]
  exact Subgroup.card_subgroup_dvd_card ρ.range
/--
[GaloisRep_exists_intermediateField_isGalois_fixingSubgroup_eq_ker](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRep_exists_intermediateField_isGalois_fixingSubgroup_eq_ker.lean)
-/
@[path]
private lemma main
    {G : Type*} [Group G] [Finite G] (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (hM : FiniteDimensional ℚ M)
    (hker : M.fixingSubgroup ≤ ρ.ker) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      F.fixingSubgroup = ρ.ker ∧ Module.finrank ℚ F ∣ Nat.card G :=
  exists_kernelField ρ M hM hker

-- created on 2026-10-20
