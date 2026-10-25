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
import Instance.AlgebraicCurve_CurveModelSmooth

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
