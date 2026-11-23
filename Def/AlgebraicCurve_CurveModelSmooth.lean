module

public import Theorem.Scheme.CurveModel
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
public import Instance.AlgebraicCurve_CurveModelSmooth

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial MvPolynomial Algebra IntermediateField IsLocalRing
open IntermediateField.algebraAdjoinAdjoin TensorProduct

universe u

namespace AlgebraicCurve.CurveModel

noncomputable def freeSubmersivePresentation (R : Type u) [CommRing R] (ι : Type) :
    SubmersivePresentation R (MvPolynomial ι R) ι (PEmpty : Type) where
  __ := Generators.mvPolynomial R ι
  relation := PEmpty.elim
  span_range_relation_eq_ker := by simp [Set.range_eq_empty, Generators.ker_mvPolynomial]
  map := PEmpty.elim
  map_inj := fun a => a.elim
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.jacobian, LinearMap.det_eq_one_of_subsingleton, map_one]
    exact isUnit_one

end AlgebraicCurve.CurveModel

end
