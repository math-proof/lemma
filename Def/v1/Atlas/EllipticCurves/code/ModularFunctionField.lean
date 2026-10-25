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
open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup


noncomputable section

namespace ModularFunctionField

/-- The function field $\mathcal{F}(\Gamma)$ of a subgroup $\Gamma \leq \mathrm{SL}_2(\mathbb{Z})$:
the type of meromorphic modular functions $f : \mathcal{H} \to \mathbb{C}$ invariant under
$\Gamma$ and meromorphic at the cusps (Definition 19.2). -/
def FunctionField (Γ : Subgroup SL(2, ℤ)) : Type :=
  {f : ℍ → ℂ // IsModularFunction f Γ}

/-- The underlying function $\mathcal{H} \to \mathbb{C}$ of an element of `FunctionField Γ`. -/
def FunctionField.toFun {Γ : Subgroup SL(2, ℤ)} (f : FunctionField Γ) : ℍ → ℂ := f.val

/-- The proof that an element of `FunctionField Γ` is in fact a modular function for $\Gamma$. -/
def FunctionField.isModular {Γ : Subgroup SL(2, ℤ)} (f : FunctionField Γ) :
    IsModularFunction f.val Γ := f.property

end ModularFunctionField
end
