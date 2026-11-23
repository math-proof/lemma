/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.SeparableClosure
public import Theorem.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part3

@[expose] public section

open groupCohomology


namespace ContCrossedHom

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]
    [TopologicalSpace G] [TopologicalSpace A]

/-- The zero continuous crossed homomorphism $\alpha \equiv 0$, which is continuous as a constant
function. -/
def zero : ContCrossedHom G A where
  toCrossedHom := CrossedHom.zero
  continuous_toFun := continuous_const

/-- Pointwise sum of two continuous crossed homomorphisms is again continuous. -/
def add (α β : ContCrossedHom G A) : ContCrossedHom G A where
  toCrossedHom := CrossedHom.add α.toCrossedHom β.toCrossedHom
  continuous_toFun := α.continuous.add β.continuous

/-- Pointwise negation of a continuous crossed homomorphism is continuous. -/
def neg (α : ContCrossedHom G A) : ContCrossedHom G A where
  toCrossedHom := CrossedHom.neg α.toCrossedHom
  continuous_toFun := α.continuous.neg

end ContCrossedHom
