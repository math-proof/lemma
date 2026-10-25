import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SmoothnessOmega
open KaehlerDifferential Algebra
open AlgebraicGeometry


/--
[krullDim_le_embDim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma krullDim_le_embDim
  {R : Type u}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  ringKrullDim R ≤ ↑(embDim R) := by
-- proof
  have h1 := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
    (IsLocalRing.maximalIdeal R) (IsLocalRing.ringJacobson_eq_maximalIdeal R ▸ le_refl _)
  have h2 : ringKrullDim (R ⧸ (IsLocalRing.maximalIdeal R : Ideal R)) = 0 :=
    ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp
        (IsLocalRing.maximalIdeal.isMaximal R))
  rwa [h2, zero_add] at h1

/--
[isRegularLocal_of_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma isRegularLocal_of_field
  {R : Type u}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R]
-- given
  (hR : IsField R) :
-- imply
  IsRegularLocal R := by
-- proof
  unfold IsRegularLocal embDim
  simp [ringKrullDim_eq_zero_of_isField hR, IsLocalRing.isField_iff_maximalIdeal_eq.mp hR,
    Submodule.spanFinrank_bot]
section FormalSmoothnessKahler
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/--
[formallySmooth_implies_kahler_projective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma formallySmooth_implies_kahler_projective
  {R : Type u}
  {A : Type v}
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  [FormallySmooth R A] :
-- imply
  Module.Projective A Ω[A⁄R] :=
-- proof
  FormallySmooth.projective_kaehlerDifferential

/--
[formallySmooth_iff_projective_and_H1_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma formallySmooth_iff_projective_and_H1_vanishes
  {R : Type u}
  {A : Type v}
  [CommRing R]
  [CommRing A]
  [Algebra R A] :
-- imply
  FormallySmooth R A ↔ Module.Projective A Ω[A⁄R] ∧ Subsingleton (H1Cotangent R A) :=
-- proof
  formallySmooth_iff R A
end FormalSmoothnessKahler
section SmoothLocusSection
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/--
[smoothLocus_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma smoothLocus_isOpen
  {R : Type u}
  {A : Type v}
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  [FinitePresentation R A] :
-- imply
  IsOpen (Algebra.smoothLocus R A) :=
-- proof
  Algebra.isOpen_smoothLocus

/--
[smoothLocus_eq_kahler_free_locus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma smoothLocus_eq_kahler_free_locus
  {R : Type u}
  {A : Type v}
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  [EssFiniteType R A] :
-- imply
  Algebra.smoothLocus R A = (Module.support A (H1Cotangent R A))ᶜ ∩ Module.freeLocus A Ω[A⁄R] :=
-- proof
  Algebra.smoothLocus_eq_compl_support_inter

/--
[smoothLocus_eq_univ_of_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma smoothLocus_eq_univ_of_smooth
  {R : Type u}
  {A : Type v}
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  [Smooth R A] :
-- imply
  Algebra.smoothLocus R A = Set.univ :=
-- proof
  Algebra.smoothLocus_eq_univ

/--
[smooth_iff_smoothLocus_univ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma smooth_iff_smoothLocus_univ
  {R : Type u}
  {A : Type v}
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  [FinitePresentation R A] :
-- imply
  Algebra.smoothLocus R A = Set.univ ↔ FormallySmooth R A :=
-- proof
  Algebra.smoothLocus_eq_univ_iff

/--
[exists_localization_smooth_of_smooth_at](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma exists_localization_smooth_of_smooth_at
  {R : Type u}
  {A : Type v}
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  [FinitePresentation R A]
  {p : Ideal A}
  [p.IsPrime]
  [IsSmoothAt R p] :
-- imply
  ∃ f ∉ p, Smooth R (Localization.Away f) :=
-- proof
  IsSmoothAt.exists_notMem_smooth R p
end SmoothLocusSection
section SmoothLocusAlgebraicDense
variable {K : Type u} [Field K] [PerfectField K]
  {A : Type u} [CommRing A] [IsDomain A] [Algebra K A]
  [Algebra.FiniteType K A]

/--
[isField_localization_atPrime_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma isField_localization_atPrime_bot
  {K : Type u}
  [Field K]
  [PerfectField K] :
-- imply
  IsField (Localization.AtPrime (⊥ : Ideal A)) := by
-- proof
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  symm; rw [← Localization.AtPrime.eq_maximalIdeal_iff_comap_eq]; simp

/--
[isSmoothAt_genericPoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma isSmoothAt_genericPoint
  {K : Type u}
  [Field K]
  [PerfectField K] :
-- imply
  Algebra.IsSmoothAt K (⊥ : Ideal A) := by
-- proof
  letI : Field (Localization.AtPrime (⊥ : Ideal A)) :=
    isField_localization_atPrime_bot.toField
  haveI : Algebra.EssFiniteType K (Localization.AtPrime (⊥ : Ideal A)) :=
    Algebra.instEssFiniteTypeLocalization K A _
  exact Algebra.FormallySmooth.of_perfectField

/--
[smoothLocus_isDense](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma smoothLocus_isDense
  {K : Type u}
  [Field K]
  [PerfectField K]
  [Algebra.FinitePresentation K A] :
-- imply
  Dense (Algebra.smoothLocus K A) := by
-- proof
  haveI := PrimeSpectrum.irreducibleSpace (R := A)
  apply IsOpen.dense Algebra.isOpen_smoothLocus
  exact ⟨⟨⊥, Ideal.isPrime_bot⟩, isSmoothAt_genericPoint⟩

/--
[smoothLocus_isOpen_and_dense](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma smoothLocus_isOpen_and_dense
  {K : Type u}
  [Field K]
  [PerfectField K]
  [Algebra.FinitePresentation K A] :
-- imply
  IsOpen (Algebra.smoothLocus K A) ∧ Dense (Algebra.smoothLocus K A) :=
-- proof
  ⟨Algebra.isOpen_smoothLocus, smoothLocus_isDense⟩
end SmoothLocusAlgebraicDense
section SmoothLocusDense
open AlgebraicGeometry
variable {X : Scheme.{u}} {K : Type u} [Field K] [PerfectField K]

/--
[smoothLocus_isDense_scheme](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma smoothLocus_isDense_scheme
  {X : Scheme.{u}}
  {K : Type u}
  [Field K]
  [PerfectField K]
  [IsReduced X]
  {f : X ⟶ Spec (.of K)}
  [LocallyOfFinitePresentation f] :
-- imply
  Dense (f.smoothLocus : Set X) :=
-- proof
  f.dense_smoothLocus_of_perfectField

/--
[smoothLocus_isOpen_and_dense_scheme](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma smoothLocus_isOpen_and_dense_scheme
  {X : Scheme.{u}}
  {K : Type u}
  [Field K]
  [PerfectField K]
  [IsReduced X]
  {f : X ⟶ Spec (.of K)}
  [LocallyOfFinitePresentation f] :
-- imply
  IsOpen (f.smoothLocus : Set X) ∧ Dense (f.smoothLocus : Set X) :=
-- proof
  ⟨f.smoothLocus.2, f.dense_smoothLocus_of_perfectField⟩
end SmoothLocusDense
section SmoothImpliesRegular
variable (k : Type u) [Field k]

/--
[smooth_ringKrullDim_mvPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma smooth_ringKrullDim_mvPolynomial
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  ringKrullDim (MvPolynomial (Fin n) k) = n := by
-- proof
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]; simp

/--
[smooth_ringKrullDim_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma smooth_ringKrullDim_polynomial
  {k : Type u}
  [Field k] :
-- imply
  ringKrullDim (Polynomial k) = 1 := by
-- proof
  rw [Polynomial.ringKrullDim_of_isNoetherianRing]; simp

/--
[localization_mvPoly_krullDim_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma localization_mvPoly_krullDim_le
  {k : Type u}
  [Field k]
  {n : ℕ}
  {𝔭 : Ideal (MvPolynomial (Fin n) k)}
  [𝔭.IsPrime] :
-- imply
  ringKrullDim (Localization.AtPrime 𝔭) ≤ ↑n := by
-- proof
  calc ringKrullDim (Localization.AtPrime 𝔭)
    ≤ ringKrullDim (MvPolynomial (Fin n) k) := by
      unfold ringKrullDim
      apply Order.krullDim_le_of_strictMono
        (PrimeSpectrum.comap (algebraMap _ (Localization.AtPrime 𝔭)))
      intro a b hab
      exact lt_of_le_of_ne (Ideal.comap_mono hab.le) fun heq =>
        hab.ne (PrimeSpectrum.localization_comap_injective _ 𝔭.primeCompl heq)
    _ = n := smooth_ringKrullDim_mvPolynomial k n

/--
[mvPolynomial_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma mvPolynomial_smooth
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  Smooth k (MvPolynomial (Fin n) k) :=
-- proof
  Smooth.mk

/--
[localization_mvPoly_krullDim_le_embDim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma localization_mvPoly_krullDim_le_embDim
  {k : Type u}
  [Field k]
  {n : ℕ}
  {𝔭 : Ideal (MvPolynomial (Fin n) k)}
  [𝔭.IsPrime] :
-- imply
  ringKrullDim (Localization.AtPrime 𝔭) ≤ ↑(embDim (Localization.AtPrime 𝔭)) :=
-- proof
  krullDim_le_embDim _
end SmoothImpliesRegular
section LocalPIDRegular
variable (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
  [IsPrincipalIdealRing R] [IsNoetherianRing R]

/--
[maximalIdeal_generator_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma maximalIdeal_generator_ne_zero
  {R : Type u}
  [CommRing R]
  [IsDomain R]
  [IsLocalRing R]
-- given
  (hR : ¬ IsField R) :
-- imply
  Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal R) ≠ 0 := by
-- proof
  intro h
  apply hR
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  rw [← Submodule.IsPrincipal.span_singleton_generator (IsLocalRing.maximalIdeal R)]
  simp [h]

/--
[embDim_eq_one_of_localPID](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma embDim_eq_one_of_localPID
  {R : Type u}
  [CommRing R]
  [IsDomain R]
  [IsLocalRing R]
-- given
  (hR : ¬ IsField R) :
-- imply
  embDim R = 1 := by
-- proof
  show Submodule.spanFinrank (IsLocalRing.maximalIdeal R) = 1
  rw [← Submodule.IsPrincipal.span_singleton_generator (IsLocalRing.maximalIdeal R)]
  exact Submodule.spanFinrank_singleton (maximalIdeal_generator_ne_zero R hR)

/--
[ringKrullDim_eq_one_of_localPID](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma ringKrullDim_eq_one_of_localPID
  {R : Type u}
  [CommRing R]
  [IsDomain R]
  [IsLocalRing R]
-- given
  (hR : ¬ IsField R) :
-- imply
  ringKrullDim R = 1 :=
-- proof
  IsPrincipalIdealRing.ringKrullDim_eq_one R hR

/--
[isRegularLocal_of_localPID](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma isRegularLocal_of_localPID
  {R : Type u}
  [CommRing R]
  [IsDomain R]
  [IsLocalRing R]
-- given
  (hR : ¬ IsField R) :
-- imply
  IsRegularLocal R := by
-- proof
  unfold IsRegularLocal
  rw [ringKrullDim_eq_one_of_localPID R hR, embDim_eq_one_of_localPID R hR]
  simp
end LocalPIDRegular
section DVRRegular
variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/--
[isRegularLocal_of_DVR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma isRegularLocal_of_DVR
  {R : Type u}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R] :
-- imply
  IsRegularLocal R :=
-- proof
  isRegularLocal_of_localPID R (IsDiscreteValuationRing.not_isField R)
end DVRRegular
section PowerSeriesRegular
variable (k : Type u) [Field k]

/--
[smooth_powerSeries_isDVR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma smooth_powerSeries_isDVR
  {k : Type u}
  [Field k] :
-- imply
  @IsDiscreteValuationRing (PowerSeries k) _ PowerSeries.instIsDomain :=
-- proof
  PowerSeries.instIsDiscreteValuationRing

/--
[powerSeries_ringKrullDim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma powerSeries_ringKrullDim
  {k : Type u}
  [Field k] :
-- imply
  ringKrullDim (PowerSeries k) = 1 :=
-- proof
  @IsPrincipalIdealRing.ringKrullDim_eq_one (PowerSeries k) _
    PowerSeries.instIsDomain
    (@IsDiscreteValuationRing.toIsPrincipalIdealRing _ _ PowerSeries.instIsDomain
      PowerSeries.instIsDiscreteValuationRing)
    PowerSeries.not_isField

/--
[powerSeries_not_isField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma powerSeries_not_isField
  {k : Type u}
  [Field k] :
-- imply
  ¬ IsField (PowerSeries k) :=
-- proof
  PowerSeries.not_isField

/--
[powerSeries_ringKrullDim_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma powerSeries_ringKrullDim_succ_le
  {k : Type u}
  [Field k]
  {R : Type*}
  [CommRing R] :
-- imply
  ringKrullDim R + 1 ≤ ringKrullDim (PowerSeries R) :=
-- proof
  ringKrullDim_succ_le_ringKrullDim_powerseries

/--
[mvPowerSeries_isLocalRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma mvPowerSeries_isLocalRing
  {k : Type u}
  [Field k]
  {d : ℕ} :
-- imply
  IsLocalRing (MvPowerSeries (Fin d) k) :=
-- proof
  inferInstance

/--
[powerSeries_maximalIdeal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean)
-/
@[path]
lemma powerSeries_maximalIdeal_eq
  {k : Type u}
  [Field k] :
-- imply
  IsLocalRing.maximalIdeal (PowerSeries k) = Ideal.span {PowerSeries.X} :=
-- proof
  PowerSeries.maximalIdeal_eq_span_X
end PowerSeriesRegular


-- created on 2026-10-23
