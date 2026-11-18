/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TannakaReconstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Tannaka
public import Abbrev.v1.Atlas.TensorCategories.code.TannakaReconstruction

@[expose] public noncomputable section
set_option maxHeartbeats 800000

open CategoryTheory

universe u v w

variable (k : Type u) [CommRing k] (A : Type u) [Ring A] [Algebra k A]

/-- The canonical ring homomorphism k →+* End(forget₂ (ModuleCat A) AddCommGrpCat) obtained
by composing the algebra map k → A with the Tannaka reconstruction isomorphism. -/
def endForget₂AlgebraMap : k →+* EndForget₂ A :=
  (ringEquivEndForget₂ A).toRingHom.comp (algebraMap k A)

end
