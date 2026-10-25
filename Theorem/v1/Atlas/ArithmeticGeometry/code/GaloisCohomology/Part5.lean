/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Topology.Algebra.MulAction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.SeparableClosure
import Def.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part4
open groupCohomology


section PrincipalCrossedHom

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- Every principal (1-coboundary) crossed homomorphism is itself a crossed homomorphism
(1-cocycle). -/
theorem IsPrincipalCrossedHom.isCrossedHom {α : G → A} (h : IsPrincipalCrossedHom α) :
    IsCrossedHom α := by
  obtain ⟨P, hP⟩ := h
  intro τ σ
  simp_rw [← hP]
  simp [smul_sub, mul_smul]

end PrincipalCrossedHom
