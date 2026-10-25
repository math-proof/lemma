/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/LocalRingAtPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.EllipticCurves.code.LocalRingAtPoint


namespace LocalRingAtPoint

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]

variable (P : LocalRingAtPoint k K)

/-- The local ring at a point is a local ring (it has a unique maximal ideal). -/
instance instIsLocalRing : IsLocalRing P.toValuationSubring :=
  P.toValuationSubring.isLocalRing

end LocalRingAtPoint
