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
import Theorem.v1.Atlas.Buildings.code.BNPair.BuildingsFromBNPairs
set_option linter.unusedSectionVars false

variable {B_idx : Type*} [DecidableEq B_idx]


namespace BNPair

variable {G : Type*} [Group G] {M : CoxeterMatrix B_idx}

/-- The *fundamental apartment* expressed as a set of $B$-cosets: $\{nB : n \in N\}$. -/
def fundamentalApartmentCosets (bp : BNPair G M) : Set (Set G) :=
  { X | ∃ (n : bp.N), X = bp.leftCoset (n : G) ∅ }

/-- The $g$-translate $g \cdot \mathcal{A}$ of the fundamental apartment: $\{(gn)B : n \in N\}$. -/
def translatedApartmentCosets (bp : BNPair G M) (g : G) : Set (Set G) :=
  { X | ∃ (n : bp.N), X = bp.leftCoset (g * (n : G)) ∅ }

end BNPair
