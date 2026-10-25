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
import Abbrev.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part2
open groupCohomology


section PrincipalCrossedHom

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The Krull topology on the absolute Galois group: open subgroups are stabilizers of finite
extensions. -/
noncomputable instance absGaloisGroupTopologicalSpace (k : Type*) [Field k] :
    TopologicalSpace (AbsGaloisGroup k) :=
  krullTopology k (AlgebraicClosure k)

end PrincipalCrossedHom
