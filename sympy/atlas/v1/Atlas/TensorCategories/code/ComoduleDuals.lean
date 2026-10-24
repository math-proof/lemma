/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ComoduleDuals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.CoalgebraBialgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.CoalgebraBialgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
import sympy.atlas.v1.Atlas.TensorCategories.code.HopfAlgebra
import Mathlib.LinearAlgebra.Contraction

set_option maxHeartbeats 800000

open scoped TensorProduct
open Coalgebra HopfAlgebra LinearMap

universe u v

section RightDualComodule

variable (k : Type u) [CommSemiring k] (H : Type v) [Semiring H] [HopfAlgebra k H]
variable (X : Type v) [AddCommGroup X] [Module k X]
variable [Module.Free k X] [Module.Finite k X]

/-- Uncurried form of the dual coaction map: given a coaction `π : X → X ⊗ H`, produces
the linear map `X* ⊗ X → H` obtained by combining the antipode, the original coaction,
and the evaluation pairing. -/
noncomputable def dualCoactUncurried (π : X →ₗ[k] X ⊗[k] H) :
    Module.Dual k X ⊗[k] X →ₗ[k] H :=
  (TensorProduct.lid k H).toLinearMap ∘ₗ
  (contractLeft k X).rTensor H ∘ₗ
  (TensorProduct.assoc k (Module.Dual k X) X H).symm.toLinearMap ∘ₗ
  ((HopfAlgebra.antipode k : H →ₗ[k] H).lTensor X ∘ₗ π).lTensor (Module.Dual k X)

/-- Curried version of `dualCoactUncurried`: a map `X* → (X → H)`. -/
noncomputable def dualCoactCurried (π : X →ₗ[k] X ⊗[k] H) :
    Module.Dual k X →ₗ[k] (X →ₗ[k] H) :=
  TensorProduct.curry (dualCoactUncurried k H X π)

/-- The dual coaction `X* → X* ⊗ H` on the linear dual of an `H`-comodule, used in
Corollary 1.22.6 to equip `X*` with a right `H`-comodule structure via the antipode. -/
noncomputable def dualCoaction (π : X →ₗ[k] X ⊗[k] H) :
    Module.Dual k X →ₗ[k] Module.Dual k X ⊗[k] H :=
  (dualTensorHomEquiv k X H).symm.toLinearMap ∘ₗ dualCoactCurried k H X π
