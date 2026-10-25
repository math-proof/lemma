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
import Theorem.v1.Atlas.EllipticCurves.code.ModularFunctionField
open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup


noncomputable section

namespace ModularFunctionField

/-- The inclusion of function fields induced by the inclusion $\Gamma \leq \mathrm{SL}_2(\mathbb{Z})$,
sending a modular function for the full group to the same function viewed as a modular
function for $\Gamma$. -/
def inclusionFun (Γ : Subgroup SL(2, ℤ)) : FunctionField ⊤ → FunctionField Γ :=
  fun ⟨f, hf⟩ => ⟨f, isModularFunction_of_top Γ hf⟩

end ModularFunctionField
end
