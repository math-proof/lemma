module
public import Def.v1.Atlas.Buildings.code.BNPair.NormalizerParabolicProof
public import Theorem.Nat.B.le.Closure_BruhatCell
public import Theorem.Set.BruhatCell.sub.SetG.of.In_BruhatCell.In_SetG.LeB
public import Theorem.v1.Atlas.Buildings.code.BNPair.SubgroupOverBProof
public import Def.v1.Atlas.Buildings.code.BNPair.BruhatPropertiesInstance
public import Mathlib.Tactic.Group
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/PropositionParabolics.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}


namespace PropositionParabolics

open BNPair NormalizerParabolic SubgroupOverB

/-- The conjugate Borel $n^{-1} B n = \{n^{-1} b n : b \in B\}$. -/
def conjB (bp : BNPair G M) (n : bp.N) : Set G :=
  { g : G | ∃ b ∈ bp.B, g = (n : G)⁻¹ * b * (n : G) }

end PropositionParabolics
