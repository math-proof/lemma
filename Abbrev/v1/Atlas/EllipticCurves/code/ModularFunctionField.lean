/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularFunctionField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.ModularPolynomial.Part5
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ModularPolynomial
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Def.v1.Atlas.EllipticCurves.code.ModularFunctionField.Part2
open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup


noncomputable section

namespace ModularFunctionField

/-- The function field $\mathcal{F}(\Gamma)$ carries a (noncanonical) field structure
(Theorem 19.8). The construction proceeds by exhibiting pointwise sum, product,
and inverse operations on the underlying functions. -/
abbrev RatFuncJ : Type := FunctionField ⊤

end ModularFunctionField
end
