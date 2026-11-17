/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.AlgebraicGeometry.Scheme
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone.Part2
open Polynomial

public section

namespace Lec20TangentCone

universe u

variable {R : Type u} [CommRing R]

/-- The scaling endomorphism of the Rees algebra fixes the image of `R` under the structure map. -/
lemma scaleOnRees_algebraMap (I : Ideal R) (c : R) (r : R) :
    scaleOnRees I c (algebraMap R (reesAlgebra I) r) = algebraMap R (reesAlgebra I) r :=
  Subtype.ext ((scaleAlgHom c).commutes r)

end Lec20TangentCone
