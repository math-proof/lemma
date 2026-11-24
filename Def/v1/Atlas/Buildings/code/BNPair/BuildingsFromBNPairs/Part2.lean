module
public import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
public import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
public import Theorem.Nat.NonemptyBruhatCell
public import Theorem.Set.All_In_StandardParabolic
public import Theorem.Nat.B.le.Closure_BruhatCell
public import Theorem.v1.Atlas.Buildings.code.BNPair.ConjugatorProof
public import Def.v1.Atlas.Buildings.code.BNPair.NormalizerParabolicProof
public import Mathlib.Tactic.Group
public import Theorem.v1.Atlas.Buildings.code.BNPair.BuildingsFromBNPairs
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

/-- The *fundamental apartment* expressed as a set of $B$-cosets: $\{nB : n \in N\}$. -/
def fundamentalApartmentCosets (bp : BNPair G M) : Set (Set G) :=
  { X | ∃ (n : bp.N), X = bp.leftCoset (n : G) ∅ }

/-- The $g$-translate $g \cdot \mathcal{A}$ of the fundamental apartment: $\{(gn)B : n \in N\}$. -/
def translatedApartmentCosets (bp : BNPair G M) (g : G) : Set (Set G) :=
  { X | ∃ (n : bp.N), X = bp.leftCoset (g * (n : G)) ∅ }

end BNPair
