-- Carved from Lemma/Definitions/Def_AlgebraicCurve_CurveModelSmooth.lean: instance decls only.
import Lemma.AlgebraicCurve.CurveModel
import Instance.JacJ1_ChartAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Extension.Presentation.Submersive
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Lemma.AlgebraicCurve.CurveModelSmooth

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial MvPolynomial Algebra IntermediateField IsLocalRing
open IntermediateField.algebraAdjoinAdjoin TensorProduct

universe u

namespace AlgebraicCurve.CurveModel

scoped instance isStandardSmoothOfRelativeDimension_polynomial (R : Type u) [CommRing R] :
    IsStandardSmoothOfRelativeDimension 1 R R[X] := by
  have h : IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial PUnit R) :=
    (freeSubmersivePresentation R PUnit).isStandardSmoothOfRelativeDimension
      (by simp [Presentation.dimension])
  exact IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1) (R := R)
    (S := MvPolynomial PUnit R) (MvPolynomial.uniqueAlgEquiv R PUnit)

variable (K : Type u) [Field K]

variable {L : Type u} [Field L] [Algebra K L]


instance chartRing_finitePresentation [CharZero K] (s : L) [FiniteDimensional K⟮s⟯ L] :
    FinitePresentation K (chartRing K ({s} : Set L)) :=
  (Algebra.FinitePresentation.of_finiteType (R := K)).mp inferInstance


end AlgebraicCurve.CurveModel

end
