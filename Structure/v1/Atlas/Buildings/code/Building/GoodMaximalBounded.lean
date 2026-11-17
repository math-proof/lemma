/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GoodMaximalBounded.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.Buildings.code.Building.FixedPointSubgroups
public import Theorem.Set.NonemptyOrbitSetSetGt
public import Def.v1.Atlas.Buildings.code.Building.GoodMaximalBounded
set_option maxHeartbeats 1600000

set_option linter.unusedSectionVars false


public noncomputable section

open Set

namespace GoodMaximalBounded

/-- The data needed to construct good maximal bounded subgroups of $G^t$: a
generalised BN-pair, bornologies on $G$ and $G^t$, a linear-part homomorphism
on $W$, existence of a good maximal bounded subgroup $K_0$ in $G$, and
bornological compatibility between the two groups. -/
structure GoodBoundedSetup (Gt : Type*) [Group Gt] {B_idx : Type*}
    (M : CoxeterMatrix B_idx) where
  gbnpair : GeneralizedBNPair Gt M
  bornG : CompactSubgroups.GroupBornology (gbnpair.G : Set Gt).Elem
  bornGt : CompactSubgroups.GroupBornology Gt
  linearPart : M.Group →* M.Group
  K₀_exists : Nonempty (CompactSubgroups.GoodMaximalBounded
    gbnpair.strictBNPair bornG linearPart)
  bornology_compatible : BornologyLiftCompatible gbnpair bornG bornGt

end GoodMaximalBounded
end
