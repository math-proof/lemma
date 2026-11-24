module
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.AlgebraicGeometry.Scheme
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone.Part4
open Polynomial


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace Lec20TangentCone

universe u

variable {R : Type u} [CommRing R]

/-- The commutative ring structure on the associated graded ring, inherited from
the quotient construction. -/
noncomputable instance assocGradedRing.commRing (𝔪 : Ideal R) :
    CommRing (assocGradedRing 𝔪) :=
  Ideal.Quotient.commRing (reesIdealFromBase 𝔪)

end Lec20TangentCone
