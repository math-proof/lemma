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
import Def.v1.Atlas.Buildings.code.CoxeterGroup.SignedPermGroup
set_option maxHeartbeats 800000


namespace SignedPerm

/-- The signed permutation group (hyperoctahedral group) $S_n^\pm = (\{\pm 1\})^n \rtimes S_n$,
the Coxeter group of type $C_n$ (Section 10.2). -/
abbrev SignedPermGroup (n : ℕ) := SignGroup n ⋊[signGroupPermAction n] Equiv.Perm (Fin n)

end SignedPerm
