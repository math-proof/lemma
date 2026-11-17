/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ReflexiveSheaves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Ideal.Basic


@[expose] public noncomputable section

namespace ReflexiveSheaf

open Module

/-- The dual sheaf `F^∨ = Hom_R(F, R)` of a module `M`, the local analog of
the dual of a sheaf of `𝒪_X`-modules. -/
abbrev dualSheaf (R : Type*) (M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] :=
  Module.Dual R M

/-- The double dual sheaf `F^{∨∨}` of a module, the target of the reflexivity
map `F → F^{∨∨}`. -/
abbrev doubleDualSheaf (R : Type*) (M : Type*)
    [CommSemiring R] [AddCommMonoid M] [Module R M] :=
  Module.Dual R (Module.Dual R M)

/-- The reflexivity map `F → F^{∨∨}`, evaluation at the dual. -/
abbrev doubleDualMap (R : Type*) (M : Type*)
    [CommSemiring R] [AddCommMonoid M] [Module R M] :
    M →ₗ[R] doubleDualSheaf R M :=
  Module.Dual.eval R M

end ReflexiveSheaf
end
