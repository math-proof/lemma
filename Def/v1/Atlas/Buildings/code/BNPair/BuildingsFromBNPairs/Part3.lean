module
public import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
public import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
public import Theorem.Nat.NonemptyBruhatCell
public import Theorem.Set.All_In_StandardParabolic
public import Theorem.Nat.B.le.Closure_BruhatCell
public import Theorem.v1.Atlas.Buildings.code.BNPair.ConjugatorProof
public import Def.v1.Atlas.Buildings.code.BNPair.NormalizerParabolicProof
public import Mathlib.Tactic.Group
public import Theorem.v1.Atlas.Buildings.code.BNPair.BuildingsFromBNPairs.Part2
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

/-- *Proper parabolics*: conjugates $g P_{S'} g^{-1}$ of proper standard parabolics ($S' \subsetneq S$). -/
def properParabolics (bp : BNPair G M) : Set (Set G) :=
  { Q | ∃ (g : G) (S' : Set B_idx), S' ≠ Set.univ ∧
    Q = bp.conjugateParabolic g S' }

/-- Concrete representative of the conjugation map sending a coset $gP_{S'}$ to its conjugate parabolic. -/
def conjugationMapRepr (bp : BNPair G M) (g : G) (S' : Set B_idx) : Set G :=
  bp.conjugateParabolic g S'

end BNPair
