/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignedPermGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Perm
set_option maxHeartbeats 800000


namespace SignedPerm

/-- The sign group $(\{\pm 1\})^n$ realized multiplicatively as $\operatorname{Fin}(n) \to (\mathbb{Z}/2)^\times$. -/
abbrev SignGroup (n : ℕ) := Fin n → Multiplicative (ZMod 2)

end SignedPerm
