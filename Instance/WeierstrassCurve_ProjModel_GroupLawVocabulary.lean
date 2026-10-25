-- Carved from Lemma/Definitions/Def_WeierstrassCurve_ProjModel_GroupLawVocabulary.lean: instance decls only.
import Lemma.WeierstrassCurve.ProjModel
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
import Lemma.WeierstrassCurve.ProjModel_GroupLawVocabulary

set_option Elab.async false


section MEGA_KwLRSymOnCurve_lean
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial WeierstrassCurve ProjWeierstrassCubicPrime

namespace WeierstrassProjModel

universe u v

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


instance kw_lrSymOC_isDomain_ℬ₀ : IsDomain ℬ₀ :=
  kw_lrSymOC_isDomain_quot_span_poly kw_lrSymOC_W₀.toProjective

end WeierstrassProjModel

end

end MEGA_KwLRSymOnCurve_lean


section MEGA_KwLRChartHomAway_lean
set_option autoImplicit false

noncomputable section

open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading

namespace WeierstrassProjModel


universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

instance kw_lrChart_biGrading_gradedAlgebra :
    GradedAlgebra (kw_lrComul_biGrading W) := inferInstance

end WeierstrassProjModel

end

end MEGA_KwLRChartHomAway_lean


section MEGA_A1_Properness_lean

set_option autoImplicit false

namespace WeierstrassProjModel

open HomogeneousIdealQuotientGrading


section QuotGradingSubmoduleDegreeZero

variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A] [AddMonoid ι]
variable (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜]
variable (I : Ideal A)

instance quotGradingSubmoduleDegreeZeroFiniteType [Algebra.FiniteType (𝒜 0) A] :
    Algebra.FiniteType ((quotGradingSubmodule 𝒜 I) 0) (A ⧸ I) :=
  quotGradingSubmodule_degreeZero_finiteType 𝒜 I ‹_›

end QuotGradingSubmoduleDegreeZero

section MvPolynomialVenue

open MvPolynomial

instance homogeneousSubmoduleDegreeZeroFiniteType (σs R : Type*) [Finite σs] [CommRing R] :
    Algebra.FiniteType ((homogeneousSubmodule σs R) 0) (MvPolynomial σs R) :=
  finiteType_gradeZero_of_finiteType_base (homogeneousSubmodule σs R) inferInstance

end MvPolynomialVenue


end WeierstrassProjModel

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime

namespace WeierstrassProjModel


variable {R : Type*} [CommRing R]

instance projModel_isIso_spec_mapCR (V : WeierstrassCurve.Projective R) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))) :=
  inferInstanceAs (IsIso (projModelSpecDegreeZeroIsoCR V).hom)

instance isProper_projModelStrCR (V : WeierstrassCurve.Projective R) :
    IsProper (projModelStrCR V) := by
  show IsProper (Proj.toSpecZero (projModelGradingCR V) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0))))
  infer_instance

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


universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


section ToTensor

variable (i j k : Fin 3)

instance kw_lrChart_tensorCommRing : CommRing ((𝒜 i) ⊗[R] (𝒜 j)) := inferInstance

end ToTensor


end WeierstrassProjModel

end

end MEGA_KwLRChartHomToTensor_lean


