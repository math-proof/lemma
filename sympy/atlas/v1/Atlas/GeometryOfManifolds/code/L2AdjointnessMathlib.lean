/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/L2AdjointnessMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.HodgeStarMathlib

open scoped Manifold ComplexConjugate
open MeasureTheory
set_option autoImplicit false

noncomputable section

namespace L2AdjointnessMathlib

open HodgeStarMathlib

/-- The Dolbeault operator $\bar\partial : \Omega^{p,q}(M) \to \Omega^{p,q+1}(M)$ on a complex
manifold $M$, here applied to smooth forms of total degree $k$, producing one of degree $k+1$. -/
end L2AdjointnessMathlib

end
