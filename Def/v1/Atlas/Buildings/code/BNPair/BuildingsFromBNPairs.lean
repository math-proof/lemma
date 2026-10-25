/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BuildingsFromBNPairs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
import Lemma.Nat.NonemptyBruhatCell
import Lemma.Set.All_In_StandardParabolic
import Lemma.Nat.B.le.Closure_BruhatCell
import Theorem.v1.Atlas.Buildings.code.BNPair.ConjugatorProof
import Def.v1.Atlas.Buildings.code.BNPair.NormalizerParabolicProof
import Mathlib.Tactic.Group
set_option linter.unusedSectionVars false

variable {B_idx : Type*} [DecidableEq B_idx]


namespace BNPair

variable {G : Type*} [Group G] {M : CoxeterMatrix B_idx}

/-- *Special subsets* of $G$: left cosets $g \cdot P_{S'}$ of a *proper* standard parabolic
$P_{S'}$ ($S' \subsetneq S$). These index the chambers and facets of the building. -/
def specialSubsets (bp : BNPair G M) : Set (Set G) :=
  { X | ∃ (g : G) (S' : Set B_idx), S' ≠ Set.univ ∧
    X = (fun x => g * x) '' bp.standardParabolic S' }

/-- The left coset $g \cdot P_{S'}$ of the standard parabolic indexed by $S'$. -/
def leftCoset (bp : BNPair G M) (g : G) (S' : Set B_idx) : Set G :=
  (fun x => g * x) '' bp.standardParabolic S'

/-- The *fundamental coset* at the identity: the standard parabolic $P_{S'}$ itself. -/
def fundamentalCoset (bp : BNPair G M) (S' : Set B_idx) : Set G :=
  bp.standardParabolic S'

/-- The *conjugate parabolic* $g P_{S'} g^{-1}$ — the image of $P_{S'}$ under conjugation by $g$. -/
def conjugateParabolic (bp : BNPair G M) (g : G) (S' : Set B_idx) : Set G :=
  (fun x => g * x * g⁻¹) '' bp.standardParabolic S'

end BNPair
