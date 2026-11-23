/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutMultiplicitySum.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutMultiplicitySum
public import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec5BezoutPascal

@[expose] public section

open MvPolynomial Classical


noncomputable section

namespace Lec5BezoutPascal

variable (k : Type*) [Field k]

/-- The vanishing locus of a plane curve `C` as a subset of `P^2`. -/
def PlaneCurve.vanishingLocus (C : PlaneCurve k) : Set (P2 k) :=
  {p | P2.liesOn k p C.poly}

/-- Two plane curves have no common irreducible component iff their defining polynomials are
coprime. -/
def PlaneCurve.noCommonComponent (C₁ C₂ : PlaneCurve k) : Prop :=
  IsCoprime C₁.poly C₂.poly

/-- The set of intersection points of two plane curves: the intersection of their vanishing loci
in `P^2`. -/
def PlaneCurve.intersectionPoints (C₁ C₂ : PlaneCurve k) : Set (P2 k) :=
  C₁.vanishingLocus k ∩ C₂.vanishingLocus k

/-- Three points in `P^2` are *collinear* if some nonzero linear form vanishes at all of them. -/
def P2Collinear (p q r : P2 k) : Prop :=
  ∃ (L : MvPolynomial (Fin 3) k),
    L ≠ 0 ∧ L.IsHomogeneous 1 ∧
    P2.liesOn k p L ∧ P2.liesOn k q L ∧ P2.liesOn k r L

/-- A plane curve is a *conic* if its degree is `2`. -/
def IsConic (C : PlaneCurve k) : Prop := C.deg = 2

/-- Defining linear form of the line through two points of `P^2`, given by the cross product of
their representatives. -/
def lineThroughPoints (p q : P2 k) : MvPolynomial (Fin 3) k :=
  let pv := Projectivization.rep p
  let qv := Projectivization.rep q
  C (pv 1 * qv 2 - pv 2 * qv 1) * X 0 +
  C (pv 2 * qv 0 - pv 0 * qv 2) * X 1 +
  C (pv 0 * qv 1 - pv 1 * qv 0) * X 2

end Lec5BezoutPascal
end
