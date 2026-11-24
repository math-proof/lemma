module
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.AlgebraicGeometry.Scheme
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone.Part6
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

/-- The associated graded ring is an algebra over the residue field `R ⧸ 𝔪`. -/
noncomputable instance assocGradedRing.algebraQuot (𝔪 : Ideal R) :
    Algebra (R ⧸ 𝔪) (assocGradedRing 𝔪) := by
  unfold assocGradedRing
  apply Ideal.Quotient.algebraQuotientOfLEComap
  intro r hr
  show r ∈ (reesIdealFromBase 𝔪).comap (algebraMap R (reesAlgebra 𝔪))
  rw [Ideal.mem_comap]
  exact Ideal.mem_map_of_mem _ hr

/-- The associated graded ring is an algebra over the Rees algebra via the quotient map. -/
noncomputable instance assocGradedRing.algebraRees (𝔪 : Ideal R) :
    Algebra (↥(reesAlgebra 𝔪)) (assocGradedRing 𝔪) := by
  unfold assocGradedRing; exact Ideal.Quotient.algebra _

end Lec20TangentCone
