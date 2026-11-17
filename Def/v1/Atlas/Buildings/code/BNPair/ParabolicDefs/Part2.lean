/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/ParabolicDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
public import Mathlib.Tactic.Group
public import Theorem.v1.Atlas.Buildings.code.BNPair.ParabolicDefs

@[expose] public section

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}


namespace BNPair

/-- The Weyl-side description of a subgroup $P$ containing $B$: the set
$\{w \in W : BwB \subseteq P\}$. For $P = P_{S'}$ this recovers $W_{S'}$. -/
def weylGroupOfParabolic (bp : BNPair G M) (P : Subgroup G)
    (_ : bp.B ≤ P) : Set M.Group :=
  { w : M.Group | bp.bruhatCell w ⊆ (P : Set G) }

end BNPair
