import Structure.WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Lemma.WeierstrassCurve.ProjModel_AddFormulas

set_option Elab.async false

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

local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R
local notation "WP₁" => kw_lrAdd_WP₁ W
local notation "WP₂" => kw_lrAdd_WP₂ W

section Abstract

variable {S : Type u} [CommRing S] [Algebra R S]

end Abstract

end WeierstrassProjModel

end

end MEGA_KwLRSymOnCurveScaled_lean

section MEGA_KwLRSymOnCurve_lean
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial WeierstrassCurve ProjWeierstrassCubicPrime

namespace WeierstrassProjModel

universe u v

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Map

variable {S : Type v} [CommRing S] (f : R →+* S)

end Map

local notation "R₀" => MvPolynomial (Fin 5) ℤ

abbrev kw_lrSymOC_W₀ : WeierstrassCurve R₀ := ⟨X 0, X 1, X 2, X 3, X 4⟩

local notation "W₀" => kw_lrSymOC_W₀
local notation "P₆₀" => MvPolynomial (Fin 3 ⊕ Fin 3) R₀
local notation "WP₁₀" => kw_lrAdd_WP₁ W₀
local notation "WP₂₀" => kw_lrAdd_WP₂ W₀

section EngineHelpers

variable {F : Type*} [CommRing F]

end EngineHelpers

section Engine

variable {F : Type*} [CommRing F] [IsDomain F] (V : WeierstrassCurve.Projective F)

end Engine

abbrev kw_lrSymOC_ℬ₀ :=
  MvPolynomial (Fin 3) R₀ ⧸ Ideal.span {kw_lrSymOC_W₀.toProjective.polynomial}

local notation "ℬ₀" => kw_lrSymOC_ℬ₀

end WeierstrassProjModel

end

end MEGA_KwLRSymOnCurve_lean

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

local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R
local notation "WP₁" => kw_lrAdd_WP₁ W
local notation "WP₂" => kw_lrAdd_WP₂ W
local notation "ℬ" => ProjModelRingCR W.toProjective

section TensorBridge

open Algebra.TensorProduct

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

local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R
local notation "ℬ" => ProjModelRingCR W.toProjective

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

set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective
set_option quotPrecheck false in
set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in

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

set_option quotPrecheck false in

local notation "𝒜" i =>
  HomogeneousLocalization.Away (projModelGradingCR V)
    (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))

end ChartStructureMap

end WeierstrassProjModel

end
end MEGA_KwProjPullbackAwayCoverCR_lean

section MEGA_A1_Properness_lean

set_option autoImplicit false

namespace WeierstrassProjModel

open HomogeneousIdealQuotientGrading

section FiniteTypeEngine

variable {ι A σ τ : Type*}
variable [CommRing A] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜]
variable (I : Ideal A)
variable [SetLike τ (A ⧸ I)] [AddSubmonoidClass τ (A ⧸ I)] (ℬ : ι → τ) [SetLike.GradedMonoid ℬ]

end FiniteTypeEngine

section BaseUpgrade

variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A] [AddMonoid ι]
variable (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜]

end BaseUpgrade

section QuotGradingSubmoduleDegreeZero

variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A] [AddMonoid ι]
variable (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜]
variable (I : Ideal A)

end QuotGradingSubmoduleDegreeZero

section MvPolynomialVenue

open MvPolynomial

end MvPolynomialVenue

section DegreeZeroEngine


end DegreeZeroEngine

section PolynomialDegreeZero

open MvPolynomial


end PolynomialDegreeZero

section ConstantCoeffKernel

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

end ConstantCoeffKernel

section DegreeZeroIdentification

open MvPolynomial

variable {σ R : Type*} [CommRing R]
variable (I : Ideal (MvPolynomial σ R))

end DegreeZeroIdentification

end WeierstrassProjModel

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type*} [CommRing R]

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

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective
set_option quotPrecheck false in
set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in

section TensorEv

variable (i j : Fin 3)

end TensorEv

section ToTensor

variable (i j k : Fin 3)

end ToTensor

section Composite

variable (i j k : Fin 3)

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

set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective
set_option quotPrecheck false in
set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in

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

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective
set_option quotPrecheck false in
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in

section ToTensor

variable (i j k : Fin 3)

end ToTensor

section Composite

variable (i j k : Fin 3)

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

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

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

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective

section ToE

variable (i j : Fin 3)

end ToE

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

end CoverCRPort

section ChartStructureMap

variable (V : WeierstrassCurve.Projective R)

set_option quotPrecheck false in

local notation "𝒜" i =>
  HomogeneousLocalization.Away (projModelGradingCR V)
    (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))


end ChartStructureMap

section PullbackCover

variable (V : WeierstrassCurve.Projective R)

end PullbackCover

section ChartIso

variable (V : WeierstrassCurve.Projective R)

set_option quotPrecheck false in

local notation "𝒜" i =>
  HomogeneousLocalization.Away (projModelGradingCR V)
    (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))


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

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective

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

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective
set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective
set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal

section NegMor

end NegMor

section GeneralNaturality


end GeneralNaturality

section NegMor2


end NegMor2

section PolyIdentity

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

end ZeroSection

section AddLawData

variable (W : WeierstrassCurve R)

local notation "E" => projModelCR W.toProjective
local notation "π" => projModelStrCR W.toProjective

end AddLawData

section Assembly

end Assembly

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

section Bridge

variable (F : Type u) [Field F] [Algebra R F]

abbrev kw_lrAptb_tF : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R F))

section Engine

end Engine

end Bridge

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

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (F : Type u) [Field F] [Algebra R F]

set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R))
set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective
set_option quotPrecheck false in
set_option quotPrecheck false in
set_option quotPrecheck false in
set_option quotPrecheck false in
local notation "t_F" => kw_lrAptb_tF (R := R) F

set_option quotPrecheck false in

section ChartClassification

end ChartClassification

section ChartFactorization

end ChartFactorization

section Forward

end Forward

section Nonsingular


end Nonsingular

section Inverse

end Inverse

section Assembly

end Assembly

end WeierstrassProjModel

end
end MEGA_KwLRAffinePtSetEquiv_lean
