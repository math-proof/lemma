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
import Theorem.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology
open groupCohomology


namespace GaloisCohomology

namespace CrossedHom

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]

/-- The zero crossed homomorphism $\alpha \equiv 0$. -/
def zero : CrossedHom G A where
  toFun := 0
  cocycle_condition τ σ := by simp [smul_zero]

/-- Pointwise addition of two crossed homomorphisms is again a crossed homomorphism. -/
def add (α β : CrossedHom G A) : CrossedHom G A where
  toFun := α + β
  cocycle_condition τ σ := by
    simp only [Pi.add_apply]
    rw [α.cocycle_condition_eq, β.cocycle_condition_eq, smul_add]
    abel

/-- Pointwise negation of a crossed homomorphism is again a crossed homomorphism. -/
def neg (α : CrossedHom G A) : CrossedHom G A where
  toFun := -α
  cocycle_condition τ σ := by
    simp only [Pi.neg_apply]
    rw [α.cocycle_condition_eq, smul_neg]
    abel

end CrossedHom
end GaloisCohomology
