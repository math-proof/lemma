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
public import Def.v1.Atlas.Buildings.code.CoxeterGroup.SignedPermGroup
@[expose] public section

set_option maxHeartbeats 800000


namespace SignedPerm

/-- The signed permutation group (hyperoctahedral group) $S_n^\pm = (\{\pm 1\})^n \rtimes S_n$,
the Coxeter group of type $C_n$ (Section 10.2). -/
abbrev SignedPermGroup (n : ℕ) := SignGroup n ⋊[signGroupPermAction n] Equiv.Perm (Fin n)

end SignedPerm
