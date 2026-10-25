/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohSpecEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
open AlgebraicGeometry CategoryTheory


noncomputable section

universe u

variable {R : CommRingCat.{u}}

/-- The adjunction `tilde ⊣ Γ` between modules over `R` and sheaves of modules
on `Spec R`. -/
def tildeΓAdjunction : tilde.functor R ⊣ moduleSpecΓFunctor :=
  tilde.adjunction

/-- The tilde functor is fully faithful, the categorical input to the
equivalence `Mod R ≃ QCoh(Spec R)`. -/
def tildeFullyFaithful : (tilde.functor R).FullyFaithful :=
  tilde.fullyFaithfulFunctor

end
