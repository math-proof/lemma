/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/UnluckyCase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.DeletionInjectivityHelpers

namespace CoxeterSystemFromDeletion

/-- The "$H$-equation" at rotation $k$: $\prod_{i=k+1}^{k+m} g_i = \prod_{i=k}^{k+m-1} g_i$. -/
def HTypeEq {W' : Type*} [Monoid W'] (g : ℕ → W') (m : ℕ) (k : ℕ) : Prop :=
  consecProd g (k + 1) m = consecProd g k m

/-- The "unlucky" case: the $H$-equation holds at every cyclic rotation $k$. -/
def AllRotationsUnlucky {W' : Type*} [Monoid W'] (g : ℕ → W') (m : ℕ) : Prop :=
  ∀ k, HTypeEq g m k
