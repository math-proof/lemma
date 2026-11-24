module
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Quotient.Card
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.ClassGroup
public import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.NumberField.Basic
public import Def.v1.Atlas.EllipticCurves.code.CMTorsor.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace IdealClassGroup

open nonZeroDivisors FractionalIdeal

section General

variable (R : Type*) [CommRing R] [IsDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K]

/-- The quotient of invertible fractional ideals by principal ones inherits an abelian
group structure. -/
noncomputable instance instCommGroupQuotient :
    CommGroup (InvertibleFractionalIdeals R K ⧸ PrincipalFractionalIdeals R K) :=
  QuotientGroup.Quotient.commGroup _

/-- The class group `Cl(R)` is an abelian group. -/
noncomputable instance : CommGroup (ClassGroup R) := inferInstance

end General
end IdealClassGroup
