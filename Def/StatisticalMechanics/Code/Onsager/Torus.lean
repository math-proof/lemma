/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Torus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace StatMech.Onsager

def onsTorusAdj (L : ℕ) (u v : ZMod L × ZMod L) : Prop :=
  (u.1 = v.1 ∧ (u.2 = v.2 + 1 ∨ u.2 = v.2 - 1)) ∨ (u.2 = v.2 ∧ (u.1 = v.1 + 1 ∨ u.1 = v.1 - 1))

end StatMech.Onsager
