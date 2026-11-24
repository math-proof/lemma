module
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.AlgebraicGeometry.Scheme
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone.Part2
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

/-- The (Zariski) tangent space scheme `Spec(Sym(T*_x X))` at the closed point. -/
noncomputable def tangentSpaceScheme : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (.of (tangentSpaceRing R))

end Lec20TangentCone
