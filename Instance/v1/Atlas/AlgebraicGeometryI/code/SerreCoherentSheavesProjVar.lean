/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreCoherentSheavesProjVar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.PicardGroup
open AlgebraicGeometry CategoryTheory TensorProduct

universe u

/-- An invertible sheaf (line bundle) on a scheme `X`: a sheaf of modules
that is locally free of rank 1. -/


noncomputable section

namespace Corollary19

section AffineCase

variable (R : Type u) [CommRing R]

/-- The Picard group of a commutative ring is naturally a commutative
group. -/
instance picardGroup_affine_commGroup : CommGroup (CommRing.Pic R) := inferInstance

end AffineCase
end Corollary19
end
