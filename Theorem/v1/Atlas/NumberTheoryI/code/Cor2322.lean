/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2322.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
universe u


lemma mapRange_linearMap_add_apply {k : Type u} [CommRing k] {α M N : Type u}
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (f g : M →ₗ[k] N) (x : α →₀ M) :
    Finsupp.mapRange.linearMap (f + g) x =
    Finsupp.mapRange.linearMap f x + Finsupp.mapRange.linearMap g x := by
  ext i
  simp [Finsupp.mapRange.linearMap]

