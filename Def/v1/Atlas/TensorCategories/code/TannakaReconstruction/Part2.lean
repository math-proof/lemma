/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TannakaReconstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Tannaka
public import Mathlib.Algebra.Algebra.Equiv
public import Instance.v1.Atlas.TensorCategories.code.TannakaReconstruction

@[expose] public noncomputable section
set_option maxHeartbeats 800000

open CategoryTheory

universe u v w

variable (k : Type u) [CommRing k] (A : Type u) [Ring A] [Algebra k A]

/-- Tannaka reconstruction for an algebra: the canonical k-algebra equivalence between
A and the endomorphism algebra of the forgetful functor ModuleCat A ⥤ AddCommGrpCat. -/
def tannakaReconstruction : A ≃ₐ[k] EndForget₂ A :=
  AlgEquiv.ofRingEquiv (f := ringEquivEndForget₂ A) (fun r => by rfl)

end
