module
public import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
public import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
public import Theorem.Nat.NonemptyBruhatCell
public import Theorem.Set.All_In_StandardParabolic
public import Theorem.Nat.B.le.Closure_BruhatCell
public import Theorem.v1.Atlas.Buildings.code.BNPair.ConjugatorProof
public import Def.v1.Atlas.Buildings.code.BNPair.NormalizerParabolicProof
public import Mathlib.Tactic.Group
public import Def.v1.Atlas.Buildings.code.BNPair.BuildingsFromBNPairs.Part4
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

/-- Defining property of the chosen representatives: $S' \neq S$ and $X$ equals $g P_{S'}$. -/
theorem specialSubsetRepr_prop (bp : BNPair G M) (X : bp.specialSubsets) :
    bp.specialSubsetReprS X ≠ Set.univ ∧
    (X : Set G) = bp.leftCoset (bp.specialSubsetReprG X) (bp.specialSubsetReprS X) :=
  (Classical.choose_spec (Classical.choose_spec X.prop)).imp_right id

/-- Second conjunct: $X$ equals the coset $g P_{S'}$ formed from the chosen representatives. -/
theorem specialSubsetRepr_eq (bp : BNPair G M) (X : bp.specialSubsets) :
    (X : Set G) = bp.leftCoset (bp.specialSubsetReprG X) (bp.specialSubsetReprS X) :=
  (specialSubsetRepr_prop bp X).2

end BNPair
