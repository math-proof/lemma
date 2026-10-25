/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GoodMaximalBounded.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.FixedPointSubgroups
import Lemma.Set.NonemptyOrbitSetSetGt
set_option maxHeartbeats 1600000

set_option linter.unusedSectionVars false


noncomputable section

open Set

namespace GoodMaximalBounded

/-- The set of generators fixing the chosen vertex $s_0$: everything in
$S \setminus \{s_0\}$. -/
def vertexFixingGenerators {B_idx : Type*} (_M : CoxeterMatrix B_idx)
    (s₀ : B_idx) : Set B_idx :=
  Set.univ \ {s₀}

/-- A permutation $\sigma$ of the generator index set stabilises the vertex
$s_0$ iff it maps the subset $S \setminus \{s_0\}$ to itself. -/
def PermStabilizesSx {B_idx : Type*} (M : CoxeterMatrix B_idx)
    (s₀ : B_idx) (σ : Equiv.Perm B_idx) : Prop :=
  ∀ s : B_idx, s ∈ vertexFixingGenerators M s₀ → σ s ∈ vertexFixingGenerators M s₀

/-- Lift a subgroup of $G \leq G^t$ to a subgroup of $G^t$ via the inclusion. -/
def liftK₀ {Gt : Type*} [Group Gt] {B_idx : Type*}
    {M : CoxeterMatrix B_idx}
    (gbnpair : GeneralizedBNPair Gt M)
    (K₀ : Subgroup (gbnpair.G : Set Gt).Elem) : Subgroup Gt :=
  K₀.map gbnpair.G.subtype

/-- The set product $\Omega' \cdot K_0$ inside $G^t$, where $K_0$ is lifted
from $G$ to $G^t$. -/
def productSetOmegaPrimeK₀ {Gt : Type*} [Group Gt] {B_idx : Type*}
    {M : CoxeterMatrix B_idx}
    (gbnpair : GeneralizedBNPair Gt M)
    (Ω' : Subgroup Gt)
    (K₀ : Subgroup (gbnpair.G : Set Gt).Elem) : Set Gt :=
  setMul (Ω' : Set Gt) ((liftK₀ gbnpair K₀ : Subgroup Gt) : Set Gt)

/-- Compatibility condition: the bornology on $G^t$ extends the one on $G$,
i.e. bounded subsets of $G$ have bounded image in $G^t$. -/
def BornologyLiftCompatible {Gt : Type*} [Group Gt] {B_idx : Type*}
    {M : CoxeterMatrix B_idx}
    (gbnpair : GeneralizedBNPair Gt M)
    (bornG : CompactSubgroups.GroupBornology (gbnpair.G : Set Gt).Elem)
    (bornGt : CompactSubgroups.GroupBornology Gt) : Prop :=
  ∀ (S : Set (gbnpair.G : Set Gt).Elem),
    bornG.isBounded S →
    bornGt.isBounded (gbnpair.G.subtype '' S)

end GoodMaximalBounded
end
