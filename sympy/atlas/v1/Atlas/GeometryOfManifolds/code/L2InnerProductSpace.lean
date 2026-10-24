/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/L2InnerProductSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.HodgeStarMathlib
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped Manifold ComplexConjugate
open MeasureTheory HodgeStarMathlib

set_option autoImplicit false

noncomputable section

namespace L2InnerProductSpace

/-- $L^2$ seminorm structure on smooth $k$-forms on a compact complex $n$-manifold,
induced by the pointwise Hermitian inner product and the volume form. -/
end L2InnerProductSpace

end
