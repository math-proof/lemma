module
public import Def.WeierstrassCurve_ProjModel
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import Def.WeierstrassCurve_ProjModel_AddFormulas
public import Instance.WeierstrassCurve_ProjModel_GroupLawVocabulary
public import Abbrev.WeierstrassCurve_ProjModel_GroupLawVocabulary
public import Notation.WeierstrassCurve_ProjModel_GroupLawVocabulary
set_option Elab.async false


public section

section MEGA_KwLRSymOnCurveScaled_lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000

noncomputable section

open MvPolynomial WeierstrassCurve

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary


end WeierstrassProjModel

end

end MEGA_KwLRSymOnCurveScaled_lean


section MEGA_KwLRAddQuotientGradedHom_lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary

def kw_lrAdd_vec : Fin 3 → P₆ := ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W]

def kw_lrComul_biIdeal : HomogeneousIdeal (homogeneousSubmodule (Fin 3 ⊕ Fin 3) R) :=
  ⟨Ideal.span {WP₁, WP₂}, kw_lrComul_biSpan_isHomogeneous W⟩

abbrev KwLRBiRing : Type u := P₆ ⧸ (kw_lrComul_biIdeal W).toIdeal


abbrev kw_lrComul_biGrading : ℕ → Submodule R (ℬ²) :=
  quotGradingSubmodule (homogeneousSubmodule (Fin 3 ⊕ Fin 3) R) (kw_lrComul_biIdeal W).toIdeal

def kw_lrAdd_substHom : MvPolynomial (Fin 3) R →ₐ[R] P₆ := aeval (kw_lrAdd_vec W)

noncomputable def kw_lrAdd_comulHom : (ℬ) →ₐ[R] (ℬ²) :=
  Ideal.Quotient.liftₐ (projModelHomogeneousIdealCR W.toProjective).toIdeal
    ((Ideal.Quotient.mkₐ R (kw_lrComul_biIdeal W).toIdeal).comp (kw_lrAdd_substHom W))
    (fun a ha => by
      refine (Ideal.Quotient.eq_zero_iff_mem).mpr ?_
      have hle : Ideal.span {W.toProjective.polynomial}
          ≤ (kw_lrComul_biIdeal W).toIdeal.comap (kw_lrAdd_substHom W).toRingHom :=
        Ideal.span_le.mpr
          (Set.singleton_subset_iff.mpr (kw_lrAdd_substHom_polynomial_mem W))
      exact hle ha)

section TensorBridge

open Algebra.TensorProduct

noncomputable def kw_lrComul_incL : (ℬ) →ₐ[R] (ℬ) ⊗[R] (ℬ) :=
  Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := ℬ) (B := ℬ)

noncomputable def kw_lrComul_incR : (ℬ) →ₐ[R] (ℬ) ⊗[R] (ℬ) :=
  Algebra.TensorProduct.includeRight (R := R) (A := ℬ) (B := ℬ)

noncomputable def kw_lrComul_tensorProj : P₆ →ₐ[R] (ℬ) ⊗[R] (ℬ) :=
  aeval (Sum.elim
    (fun i => kw_lrComul_incL W
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i)))
    (fun i => kw_lrComul_incR W
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i))))

noncomputable def kw_lrComul_biToTensor : (ℬ²) →ₐ[R] (ℬ) ⊗[R] (ℬ) :=
  Ideal.Quotient.liftₐ (kw_lrComul_biIdeal W).toIdeal (kw_lrComul_tensorProj W)
    (fun a ha => by
      have hle : Ideal.span {WP₁, WP₂} ≤ RingHom.ker (kw_lrComul_tensorProj W).toRingHom :=
        Ideal.span_le.mpr (by
          rintro p (rfl | hp)
          · exact kw_lrComul_tensorProj_WP₁ W
          · rw [Set.mem_singleton_iff] at hp; subst hp; exact kw_lrComul_tensorProj_WP₂ W)
      exact hle ha)

end TensorBridge

end WeierstrassProjModel

end

end MEGA_KwLRAddQuotientGradedHom_lean

section MEGA_KwLRSymQuotientGradedHom_lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary

def kw_lrSym_vec : Fin 3 → P₆ := ![kw_lrSym_X W, kw_lrSym_Y W, kw_lrSym_Z W]

def kw_lrSym_substHom : MvPolynomial (Fin 3) R →ₐ[R] P₆ := aeval (kw_lrSym_vec W)

noncomputable def kw_lrSym_comulHom : (ℬ) →ₐ[R] (ℬ²) :=
  Ideal.Quotient.liftₐ (projModelHomogeneousIdealCR W.toProjective).toIdeal
    ((Ideal.Quotient.mkₐ R (kw_lrComul_biIdeal W).toIdeal).comp (kw_lrSym_substHom W))
    (fun a ha => by
      refine (Ideal.Quotient.eq_zero_iff_mem).mpr ?_
      have hle : Ideal.span {W.toProjective.polynomial}
          ≤ (kw_lrComul_biIdeal W).toIdeal.comap (kw_lrSym_substHom W).toRingHom :=
        Ideal.span_le.mpr
          (Set.singleton_subset_iff.mpr (kw_lrSym_substHom_polynomial_mem W))
      exact hle ha)

end WeierstrassProjModel

end

end MEGA_KwLRSymQuotientGradedHom_lean

section MEGA_KwLRChartHomAway_lean
set_option autoImplicit false

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary


open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary.v0

set_option quotPrecheck false in


noncomputable def kw_lrChart_locMap (k : Fin 3) :
    Localization.Away (mk₃ (X k : MvPolynomial (Fin 3) R))
      →+* Localization.Away (mk₆ (kw_lrAdd_vec W k)) :=
  IsLocalization.map _ (kw_lrAdd_comulHom W).toRingHom (kw_lrChart_powers_comap_le W k)

noncomputable def kw_lrChart_aux (k : Fin 3) :
    (𝒜 k) →+* Localization.Away (mk₆ (kw_lrAdd_vec W k)) :=
  (kw_lrChart_locMap W k).comp
    (algebraMap (𝒜 k) (Localization.Away (mk₃ (X k : MvPolynomial (Fin 3) R))))

noncomputable def kw_lrChart_witness (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) : (𝒜² k) :=
  HomogeneousLocalization.Away.mk (kw_lrComul_biGrading W)
    (kw_lrChart_mkAdd_mem_four W k) n (kw_lrAdd_comulHom W a)
    (by
      have ha' : a ∈ projModelGradingCR W.toProjective n := by simpa using ha
      have h4n : kw_lrAdd_comulHom W a ∈ kw_lrComul_biGrading W (4 * n) :=
        kw_lrAdd_comulHom_graded W ha'
      simpa [smul_eq_mul, Nat.mul_comm] using h4n)

noncomputable def kw_lrChart_away (k : Fin 3) : (𝒜 k) →+* (𝒜² k) := by
  let e := RingEquiv.ofLeftInverse
    (f := algebraMap (𝒜² k) (Localization.Away (mk₆ (kw_lrAdd_vec W k))))
    (h := (HomogeneousLocalization.val_injective _).hasLeftInverse.choose_spec)
  exact RingHom.comp (e.symm.toRingHom.comp (Subring.inclusion (kw_lrChart_aux_range_le W k)))
    (kw_lrChart_aux W k).rangeRestrict

end WeierstrassProjModel

end

end MEGA_KwLRChartHomAway_lean

section MEGA_KwProjPullbackAwayCoverCR_lean
set_option autoImplicit false

noncomputable section

open MvPolynomial HomogeneousLocalization

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (R : Type u) [CommRing R]

section ChartStructureMap

variable (V : WeierstrassCurve.Projective R)


open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary.v1

@[reducible] noncomputable def kw_pbac_awayAlgebra (i : Fin 3) : Algebra R (𝒜 i) :=
  ((fromZeroRingHom (projModelGradingCR V) _).comp
    (algebraMap R ((projModelGradingCR V) 0))).toAlgebra

end ChartStructureMap

end WeierstrassProjModel

end
end MEGA_KwProjPullbackAwayCoverCR_lean

section MEGA_A1_Properness_lean

set_option autoImplicit false


noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type*} [CommRing R]

def projModelDegreeZeroRingEquivCR (V : WeierstrassCurve.Projective R) :
    R ≃+* ((projModelGradingCR V) 0) :=
  RingEquiv.ofBijective (algebraMap R ((projModelGradingCR V) 0))
    (projModel_degreeZero_algebraMap_bijectiveCR V)

def projModelSpecDegreeZeroIsoCR (V : WeierstrassCurve.Projective R) :
    Spec (CommRingCat.of ((projModelGradingCR V) 0)) ≅ Spec (CommRingCat.of R) where
  hom := Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))
  inv := Spec.map (CommRingCat.ofHom
    ((projModelDegreeZeroRingEquivCR V).symm : ((projModelGradingCR V) 0) →+* R))
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (algebraMap R ((projModelGradingCR V) 0)).comp
          ((projModelDegreeZeroRingEquivCR V).symm : ((projModelGradingCR V) 0) →+* R)
        = RingHom.id ((projModelGradingCR V) 0) from
        RingHom.ext fun x => (projModelDegreeZeroRingEquivCR V).apply_symm_apply x,
      CommRingCat.ofHom_id, Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show ((projModelDegreeZeroRingEquivCR V).symm : ((projModelGradingCR V) 0) →+* R).comp
          (algebraMap R ((projModelGradingCR V) 0))
        = RingHom.id R from
        RingHom.ext fun x => (projModelDegreeZeroRingEquivCR V).symm_apply_apply x,
      CommRingCat.ofHom_id, Spec.map_id]

end WeierstrassProjModel

end

end MEGA_A1_Properness_lean

section MEGA_KwLRChartHomToTensor_lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary
open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary.v0

noncomputable def kw_lrChart_gen (i m : Fin 3) : (𝒜 i) :=
  HomogeneousLocalization.mk
    ⟨1, ⟨mk₃ (X m : MvPolynomial (Fin 3) R), kw_lrChart_mkX_mem_one W m⟩,
        ⟨mk₃ (X i : MvPolynomial (Fin 3) R), kw_lrChart_mkX_mem_one W i⟩, ⟨1, pow_one _⟩⟩

noncomputable def kw_lrChart_dehom (i : Fin 3) :
    MvPolynomial (Fin 3) R →ₐ[R] (𝒜 i) :=
  aeval (kw_lrChart_gen W i)


section TensorEv

variable (i j : Fin 3)

noncomputable def kw_lrChart_inL : (𝒜 i) →ₐ[R] (𝒜 i) ⊗[R] (𝒜 j) :=
  Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := 𝒜 i) (B := 𝒜 j)

noncomputable def kw_lrChart_inR : (𝒜 j) →ₐ[R] (𝒜 i) ⊗[R] (𝒜 j) :=
  Algebra.TensorProduct.includeRight (R := R) (A := 𝒜 i) (B := 𝒜 j)

noncomputable def kw_lrChart_ev :
    MvPolynomial (Fin 3 ⊕ Fin 3) R →ₐ[R] (𝒜 i) ⊗[R] (𝒜 j) :=
  aeval (Sum.elim (fun m => kw_lrChart_inL W i j (kw_lrChart_gen W i m))
                  (fun m => kw_lrChart_inR W i j (kw_lrChart_gen W j m)))

noncomputable def kw_lrChart_ev' : (ℬ²) →ₐ[R] (𝒜 i) ⊗[R] (𝒜 j) :=
  Ideal.Quotient.liftₐ (kw_lrComul_biIdeal W).toIdeal (kw_lrChart_ev W i j)
    (fun a ha => by
      have hle : Ideal.span {kw_lrAdd_WP₁ W, kw_lrAdd_WP₂ W}
          ≤ RingHom.ker (kw_lrChart_ev W i j).toRingHom :=
        Ideal.span_le.mpr (by
          rintro p (rfl | hp)
          · exact kw_lrChart_ev_WP₁ W i j
          · rw [Set.mem_singleton_iff] at hp; subst hp; exact kw_lrChart_ev_WP₂ W i j)
      exact hle ha)

end TensorEv

section ToTensor

variable (i j k : Fin 3)

noncomputable def kw_lrChart_u : (𝒜 i) ⊗[R] (𝒜 j) :=
  kw_lrChart_ev' W i j (mk₆ (kw_lrAdd_vec W k))

noncomputable def kw_lrChart_toTensorLoc :
    Localization.Away (mk₆ (kw_lrAdd_vec W k))
      →+* Localization.Away (kw_lrChart_u W i j k) :=
  IsLocalization.map _ (kw_lrChart_ev' W i j).toRingHom
    (kw_lrChart_powers_ev'_comap_le W i j k)

noncomputable def kw_lrChart_toTensor :
    (𝒜² k) →+* Localization.Away (kw_lrChart_u W i j k) :=
  (kw_lrChart_toTensorLoc W i j k).comp
    (algebraMap (𝒜² k) (Localization.Away (mk₆ (kw_lrAdd_vec W k))))

end ToTensor

section Composite

variable (i j k : Fin 3)

noncomputable def kw_lrChart_tensor :
    (𝒜 k) →+* Localization.Away (kw_lrChart_u W i j k) :=
  (kw_lrChart_toTensor W i j k).comp (kw_lrChart_away W k)

end Composite

end WeierstrassProjModel

end

end MEGA_KwLRChartHomToTensor_lean

section MEGA_KwLRSymChartHomAway_lean
set_option autoImplicit false

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary


open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary.v0

set_option quotPrecheck false in


noncomputable def kw_lrSymChart_locMap (k : Fin 3) :
    Localization.Away (mk₃ (X k : MvPolynomial (Fin 3) R))
      →+* Localization.Away (mk₆ (kw_lrSym_vec W k)) :=
  IsLocalization.map _ (kw_lrSym_comulHom W).toRingHom (kw_lrSymChart_powers_comap_le W k)

noncomputable def kw_lrSymChart_aux (k : Fin 3) :
    (𝒜 k) →+* Localization.Away (mk₆ (kw_lrSym_vec W k)) :=
  (kw_lrSymChart_locMap W k).comp
    (algebraMap (𝒜 k) (Localization.Away (mk₃ (X k : MvPolynomial (Fin 3) R))))

noncomputable def kw_lrSymChart_witness (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) : (𝒜²ₛ k) :=
  HomogeneousLocalization.Away.mk (kw_lrComul_biGrading W)
    (kw_lrSymChart_mkSym_mem_four W k) n (kw_lrSym_comulHom W a)
    (by
      have ha' : a ∈ projModelGradingCR W.toProjective n := by simpa using ha
      have h4n : kw_lrSym_comulHom W a ∈ kw_lrComul_biGrading W (4 * n) :=
        kw_lrSym_comulHom_graded W ha'
      simpa [smul_eq_mul, Nat.mul_comm] using h4n)

noncomputable def kw_lrSymChart_away (k : Fin 3) : (𝒜 k) →+* (𝒜²ₛ k) := by
  let e := RingEquiv.ofLeftInverse
    (f := algebraMap (𝒜²ₛ k) (Localization.Away (mk₆ (kw_lrSym_vec W k))))
    (h := (HomogeneousLocalization.val_injective _).hasLeftInverse.choose_spec)
  exact RingHom.comp (e.symm.toRingHom.comp
      (Subring.inclusion (kw_lrSymChart_aux_range_le W k)))
    (kw_lrSymChart_aux W k).rangeRestrict

end WeierstrassProjModel

end
end MEGA_KwLRSymChartHomAway_lean

section MEGA_KwLRSymChartHomToTensor_lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary
open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary.v0

section ToTensor

variable (i j k : Fin 3)

noncomputable def kw_lrSymChart_u : (𝒜 i) ⊗[R] (𝒜 j) :=
  kw_lrChart_ev' W i j (mk₆ (kw_lrSym_vec W k))

noncomputable def kw_lrSymChart_toTensorLoc :
    Localization.Away (mk₆ (kw_lrSym_vec W k))
      →+* Localization.Away (kw_lrSymChart_u W i j k) :=
  IsLocalization.map _ (kw_lrChart_ev' W i j).toRingHom
    (kw_lrSymChart_powers_ev'_comap_le W i j k)

noncomputable def kw_lrSymChart_toTensor :
    (𝒜²ₛ k) →+* Localization.Away (kw_lrSymChart_u W i j k) :=
  (kw_lrSymChart_toTensorLoc W i j k).comp
    (algebraMap (𝒜²ₛ k) (Localization.Away (mk₆ (kw_lrSym_vec W k))))

end ToTensor

section Composite

variable (i j k : Fin 3)

noncomputable def kw_lrSymChart_tensor :
    (𝒜 k) →+* Localization.Away (kw_lrSymChart_u W i j k) :=
  (kw_lrSymChart_toTensor W i j k).comp (kw_lrSymChart_away W k)

end Composite

end WeierstrassProjModel

end

end MEGA_KwLRSymChartHomToTensor_lean

section MEGA_KwLRSixUCoverage_lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary.v0

noncomputable def kw_lrSixU (i j : Fin 3) : Fin 3 ⊕ Fin 3 → (𝒜 i) ⊗[R] (𝒜 j) :=
  Sum.elim (kw_lrChart_u W i j) (kw_lrSymChart_u W i j)

def KwLRSixUCoverage : Prop :=
  ∀ (i j : Fin 3),
    Ideal.span (Set.range (kw_lrSixU W i j)) = (⊤ : Ideal ((𝒜 i) ⊗[R] (𝒜 j)))

end WeierstrassProjModel

end
end MEGA_KwLRSixUCoverage_lean

section MEGA_KwLRPerChartGlue_lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary.v0

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary

noncomputable def kw_lrSixU_cover (i j : Fin 3)
    (h : Ideal.span (Set.range (kw_lrSixU W i j)) = ⊤) :
    (Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j)))).AffineOpenCover :=
  Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of ((𝒜 i) ⊗[R] (𝒜 j))) (kw_lrSixU W i j) h

section ToE

variable (i j : Fin 3)

noncomputable def kw_lrSixU_toE :
    ∀ l : Fin 3 ⊕ Fin 3,
      Spec (CommRingCat.of (Localization.Away (kw_lrSixU W i j l))) ⟶ E
  | .inl k => Spec.map (CommRingCat.ofHom (kw_lrChart_tensor W i j k))
      ≫ Proj.awayι (projModelGradingCR W.toProjective) _ (kw_lrChart_mkX_mem_one W k) one_pos
  | .inr k => Spec.map (CommRingCat.ofHom (kw_lrSymChart_tensor W i j k))
      ≫ Proj.awayι (projModelGradingCR W.toProjective) _ (kw_lrChart_mkX_mem_one W k) one_pos

end ToE

noncomputable def kw_lrSixU_locMap (i j : Fin 3) (l : Fin 3 ⊕ Fin 3) :
    Spec (CommRingCat.of (Localization.Away (kw_lrSixU W i j l)))
      ⟶ Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (kw_lrSixU W i j l))))

def KwLRPerChartCompat : Prop :=
  ∀ (i j : Fin 3) (l l' : Fin 3 ⊕ Fin 3),
    pullback.fst (kw_lrSixU_locMap W i j l) (kw_lrSixU_locMap W i j l')
        ≫ kw_lrSixU_toE W i j l
      = pullback.snd (kw_lrSixU_locMap W i j l) (kw_lrSixU_locMap W i j l')
        ≫ kw_lrSixU_toE W i j l'

noncomputable def kw_lrPerChart_toE (hcov : KwLRSixUCoverage W)
    (hcompat : KwLRPerChartCompat W) (i j : Fin 3) :
    Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) ⟶ E :=
  (kw_lrSixU_cover W i j (hcov i j)).openCover.glueMorphisms
    (kw_lrSixU_toE W i j) (hcompat i j)

end WeierstrassProjModel

end
end MEGA_KwLRPerChartGlue_lean

section MEGA_KwProjPullbackAwayCoverCRCover_lean
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (R : Type u) [CommRing R]

section CoverCRPort

variable (V : WeierstrassCurve.Projective R)

open MvPolynomial in

noncomputable def projModelAffineOpenCoverCR :
    Scheme.AffineOpenCover (projModelCR V) :=
  Proj.affineOpenCoverOfIrrelevantLESpan (projModelGradingCR V)
    (fun i : Fin 3 =>
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))
    (m := fun _ => 1)
    (fun i => kw_pbac_mk_X_mem_one_CR R V i) (fun _ => Nat.one_pos)
    (kw_pbac_irrelevant_le_span_mk_X_CR R V)

end CoverCRPort


section PullbackCover

variable (V : WeierstrassCurve.Projective R)

noncomputable def kwProjPullbackOpenCoverCR :
    (pullback (projModelStrCR V) (projModelStrCR V)).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight
    (projModelAffineOpenCoverCR R V).openCover
    (projModelAffineOpenCoverCR R V).openCover
    (projModelStrCR V) (projModelStrCR V)

end PullbackCover

section ChartIso

variable (V : WeierstrassCurve.Projective R)


open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary.v1

attribute [local instance] kw_pbac_awayAlgebra

noncomputable def kwProjPullbackChartIsoCR (i j : Fin 3) :
    (kwProjPullbackOpenCoverCR R V).X (i, j)
      ≅ Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) :=
  pullback.congrHom (kw_pbac_awayι_comp_projModelStrCR R V i)
      (kw_pbac_awayι_comp_projModelStrCR R V j)
    ≪≫ pullbackSpecIso R (𝒜 i) (𝒜 j)

end ChartIso

end WeierstrassProjModel

end

end MEGA_KwProjPullbackAwayCoverCRCover_lean

section MEGA_KwLROuterGlue_lean
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary

noncomputable def kw_lrOuter_toE (hcov : KwLRSixUCoverage W)
    (hcompat : KwLRPerChartCompat W) :
    ∀ ij, (kwProjPullbackOpenCoverCR R W.toProjective).X ij ⟶ E :=
  fun ij => (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).hom
            ≫ kw_lrPerChart_toE W hcov hcompat ij.1 ij.2

def KwLROuterCompat : Prop :=
  ∀ (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W)
    (ij ij' : Fin 3 × Fin 3),
    pullback.fst ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                 ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')
        ≫ kw_lrOuter_toE W hcov hcompat ij
      = pullback.snd ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                     ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')
        ≫ kw_lrOuter_toE W hcov hcompat ij'

noncomputable def kw_lrAddMorphism (hcov : KwLRSixUCoverage W)
    (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective) ⟶ E :=
  (kwProjPullbackOpenCoverCR R W.toProjective).glueMorphisms
    (kw_lrOuter_toE W hcov hcompat) (houter hcov hcompat)

end WeierstrassProjModel

end
end MEGA_KwLROuterGlue_lean

section MEGA_KwLRAddNegDiagZeroNegMor_lean
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped TensorProduct

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary.v0
open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary

section NegMor

def kw_lrAddNegDiag_negSubstGen : Fin 3 → MvPolynomial (Fin 3) R :=
  ![X 0, -X 1 - C W.a₁ * X 0 - C W.a₃ * X 2, X 2]

def kw_lrAddNegDiag_negSubst : MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  aeval (kw_lrAddNegDiag_negSubstGen W)

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary

def kw_lrAddNegDiag_negQuotHom : ℬ →+* ℬ :=
  Ideal.Quotient.lift (projModelHomogeneousIdealCR W.toProjective).toIdeal
    ((Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal).comp
      (negSubst : MvPolynomial (Fin 3) R →+* _))
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr
      ((Ideal.map_le_iff_le_comap.mp (kw_lrAddNegDiag_negSubst_mapSpan W).le)
        (projModelHomogeneousIdealCR_toIdeal W.toProjective ▸ ha)))

def kw_lrAddNegDiag_negGradedHom :
    projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR W.toProjective where
  toRingHom := kw_lrAddNegDiag_negQuotHom W
  map_mem {i x} hx := by
    obtain ⟨a, ha, rfl⟩ := (mem_quotGradingSubmodule_iff _ _).mp hx
    exact mk_mem_quotGradingSubmodule _ _
      ((mem_homogeneousSubmodule _ _).mpr
        (kw_lrAddNegDiag_negSubst_isHomogeneous W
          ((mem_homogeneousSubmodule _ _).mp ha)))


set_option linter.unnecessarySeqFocus false in

def kw_lrAddNegDiag_negMor : E ⟶ E :=
  Proj.map negGradedHom (kw_lrAddNegDiag_negGradedHom_irrelevant_le W)


end NegMor


section PolyIdentity

noncomputable def kw_lrAddNegDiag_evalNeg :
    MvPolynomial (Fin 3 ⊕ Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  aeval (Sum.elim (kw_lrAddNegDiag_negSubstGen W) X)

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary

end PolyIdentity

end WeierstrassProjModel

end

end MEGA_KwLRAddNegDiagZeroNegMor_lean

section MEGA_KwProjWeierstrassRelGroupLawConstruct_lean
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve

universe u

namespace WeierstrassProjModel

open WeierstrassProjModel NeronModelInfra HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

section ZeroSection

variable (W : WeierstrassCurve R)

open MvPolynomial in

open MvPolynomial in

def kwYEvalRingHom : ProjModelRingCR W.toProjective →+* R :=
  Ideal.Quotient.lift _ (MvPolynomial.eval ![(0 : R), 1, 0]) fun a ha => by
    refine (Ideal.span_le.mpr ?_ : Ideal.span _ ≤ RingHom.ker _)
      (projModelHomogeneousIdealCR_toIdeal W.toProjective ▸ ha)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]

    exact WeierstrassCurve.Projective.equation_zero

open MvPolynomial in

def kwYChartEval :
    HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
      (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)) →+* R :=
  (IsLocalization.Away.lift (g := kwYEvalRingHom R W)
      (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))
      (kwYEvalRingHom_mk_X1 R W ▸ isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)))
      (Localization.Away
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))))

open MvPolynomial in

def kwZeroSect : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) (projModelStrCR W.toProjective) :=
  ⟨Spec.map (CommRingCat.ofHom (kwYChartEval R W)) ≫
    Proj.awayι (projModelGradingCR W.toProjective) _ (kw_mk_X1_mem_one_CR R W) one_pos,
   by
    simp only [projModelStrCR, Category.assoc]
    rw [← Category.assoc (Proj.awayι ..), Proj.awayι_toSpecZero, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      kwYChartEval_section, CommRingCat.ofHom_id, Spec.map_id]⟩

end ZeroSection


end WeierstrassProjModel

end
end MEGA_KwProjWeierstrassRelGroupLawConstruct_lean

section MEGA_KwLRAffinePtTorsionBridge_lean

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve

namespace WeierstrassProjModel

open WeierstrassProjModel NeronModelInfra

attribute [local instance] Classical.propDecidable

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


end WeierstrassProjModel

end

end MEGA_KwLRAffinePtTorsionBridge_lean

section MEGA_KwLRAffinePtSetEquiv_lean
set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve MvPolynomial
open HomogeneousLocalization HomogeneousIdealQuotientGrading
open scoped WeierstrassCurve.Projective

namespace WeierstrassProjModel

open WeierstrassProjModel NeronModelInfra

attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] kw_pbac_awayAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (F : Type u) [Field F] [Algebra R F]

open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary
open scoped WeierstrassCurve_ProjModel_GroupLawVocabulary.v2


abbrev kw_lrApt_WF : WeierstrassCurve.Projective F := (W.baseChange F).toProjective


section ChartClassification

def kw_lrApt_chartEval (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) : Fin 3 → F :=
  fun k => ψ (gen i k)

end ChartClassification


end WeierstrassProjModel

end
end MEGA_KwLRAffinePtSetEquiv_lean
