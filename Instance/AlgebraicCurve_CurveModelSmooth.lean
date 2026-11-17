-- Carved from Lemma/Definitions/Def_AlgebraicCurve_CurveModelSmooth.lean: instance decls only.

module

public import Instance.JacJ1_ChartAlgebra
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

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
