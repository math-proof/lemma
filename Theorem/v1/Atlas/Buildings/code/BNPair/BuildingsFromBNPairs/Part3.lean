module
public import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
public import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
public import Theorem.Nat.NonemptyBruhatCell
public import Theorem.Set.All_In_StandardParabolic
public import Theorem.Nat.B.le.Closure_BruhatCell
public import Theorem.v1.Atlas.Buildings.code.BNPair.ConjugatorProof
public import Def.v1.Atlas.Buildings.code.BNPair.NormalizerParabolicProof
public import Mathlib.Tactic.Group
public import Def.v1.Atlas.Buildings.code.BNPair.BuildingsFromBNPairs.Part3
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable {B_idx : Type*} [DecidableEq B_idx]


namespace BNPair

variable {G : Type*} [Group G] {M : CoxeterMatrix B_idx}

/-- Injectivity at the coset level: equal conjugate parabolics force equal cosets. -/
theorem conjugation_injective_on_cosets (bp : BNPair G M)
    (bd : BruhatProperties bp) (ax : BNPairAxioms bp)
    (g h : G) (S₁ S₂ : Set B_idx)
    (heq : bp.conjugateParabolic g S₁ = bp.conjugateParabolic h S₂) :
    bp.leftCoset g S₁ = bp.leftCoset h S₂ := by
  apply Set.Subset.antisymm
  · exact conjugation_reflects_order bp bd ax g h S₁ S₂ heq.le
  · exact conjugation_reflects_order bp bd ax h g S₂ S₁ heq.ge

end BNPair
