/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/TKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.BNPair.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Ker

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
variable (bp : BNPair G M)


/-- The action of $N$ on the standard apartment $W$ by left translation: $n \cdot w =
\pi(n) \cdot w$. -/
def BNPair.apartmentActionFun (n : bp.N) (w : M.Group) : M.Group :=
  bp.π n * w

/-- $T$ is normal in $N$, since $T = \ker \pi$ as a subgroup of $N$. -/
instance BNPair.T_normal_in_N : (bp.T.subgroupOf bp.N).Normal := by
  rw [bp.T_subgroupOf_eq_ker]
  exact MonoidHom.normal_ker bp.π


/-- The induced homomorphism $N/T \to W$ obtained by descending $\pi : N \to W$ through
its kernel $T$. -/
noncomputable def BNPair.quotientToW :
    bp.N ⧸ (bp.T.subgroupOf bp.N) →* M.Group :=
  QuotientGroup.lift _ bp.π (by
    intro x hx
    simp [Subgroup.mem_subgroupOf] at hx
    exact (bp.π_ker x).mpr hx)

/-- **The isomorphism $N/T \cong W$.** Packages `quotientToW` and its bijectivity into a
group isomorphism, identifying the Weyl group $W$ of the Coxeter system with the
quotient $N/T$ of the BN-pair. -/
noncomputable def BNPair.quotientIso :
    bp.N ⧸ (bp.T.subgroupOf bp.N) ≃* M.Group :=
  MulEquiv.ofBijective bp.quotientToW bp.quotientToW_bijective
