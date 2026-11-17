/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignedPermGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Fintype.Perm
@[expose] public section

set_option maxHeartbeats 800000


namespace SignedPerm

/-- The sign group $(\{\pm 1\})^n$ realized multiplicatively as $\operatorname{Fin}(n) \to (\mathbb{Z}/2)^\times$. -/
abbrev SignGroup (n : ℕ) := Fin n → Multiplicative (ZMod 2)

end SignedPerm
