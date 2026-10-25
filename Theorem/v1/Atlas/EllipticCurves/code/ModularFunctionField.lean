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
import Def.v1.Atlas.EllipticCurves.code.ModularFunctionField
open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup


noncomputable section

namespace ModularFunctionField

/-- A function modular for the full group $\mathrm{SL}_2(\mathbb{Z})$ is a fortiori
modular for any subgroup $\Gamma$: meromorphicity is preserved and invariance under
$\Gamma$ follows from invariance under the whole group. -/
theorem isModularFunction_of_top {f : ℍ → ℂ} (Γ : Subgroup SL(2, ℤ))
    (hf : IsModularFunction f ⊤) : IsModularFunction f Γ where
  meromorphicOnH := hf.meromorphicOnH
  invariant := fun γ _ τ => hf.invariant γ (Subgroup.mem_top γ) τ
  meromorphicAtCusps := hf.meromorphicAtCusps

end ModularFunctionField
end
