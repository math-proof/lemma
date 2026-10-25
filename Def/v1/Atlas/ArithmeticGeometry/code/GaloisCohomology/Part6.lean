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
import Abbrev.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology
open groupCohomology


section PrincipalCrossedHom

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The canonical projection $\mathrm{ContCrossedHom}(G, A) \to H^1(G, A)$. -/
def H1.mk (α : ContCrossedHom G A) : H1 G A :=
  QuotientAddGroup.mk α

end PrincipalCrossedHom
