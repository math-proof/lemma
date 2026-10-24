/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyPicard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.AffinePushforwardCohomology
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.Flat.Localization

open AlgebraicGeometry CategoryTheory Limits
open scoped nonZeroDivisors

noncomputable section

universe u

namespace CohomologyPicard


section PicardClassGroup

end PicardClassGroup


section CohomologyVanishing


/-- Higher cohomology of a quasi-coherent sheaf on an affine scheme vanishes (Serre's
vanishing theorem for affine schemes). -/
end CohomologyVanishing

end CohomologyPicard
