/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannRochCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
set_option maxHeartbeats 1600000

open scoped TensorProduct
open nonZeroDivisors
open RiemannRochCurves CanonicalSheafCurves


noncomputable section

/-- A Dedekind curve over a field `k`: the data of a finite `k`-algebra `A` which is a
Dedekind domain. Models a smooth affine curve over `k`. -/
structure DedekindCurve (k : Type*) [Field k] where
  A : Type*
  [instCR : CommRing A]
  [instID : IsDomain A]
  [instDD : IsDedekindDomain A]
  [instAlg : Algebra k A]
  [instFin : Module.Finite k A]

end
