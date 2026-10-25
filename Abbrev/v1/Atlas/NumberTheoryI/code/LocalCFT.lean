/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open scoped RestrictedProduct
open Filter Set


section RestrictedProduct

variable {ι : Type*} (X : ι → Type*) (U : (i : ι) → Set (X i))

abbrev restrictedProduct : Type _ := Πʳ i, [X i, U i]

variable [∀ i, TopologicalSpace (X i)]

end RestrictedProduct

section DirectSystem

variable {I : Type*} [Preorder I]


abbrev IsDirectSystem (F : I → Type*) (f : ⦃i j : I⦄ → i ≤ j → F i → F j) : Prop :=
  DirectedSystem F f

end DirectSystem
