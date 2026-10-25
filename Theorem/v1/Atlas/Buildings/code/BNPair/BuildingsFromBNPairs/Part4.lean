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
import Def.v1.Atlas.Buildings.code.BNPair.BuildingsFromBNPairs.Part4
set_option linter.unusedSectionVars false

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
