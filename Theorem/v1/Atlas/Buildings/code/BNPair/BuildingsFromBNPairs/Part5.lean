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
import Def.v1.Atlas.Buildings.code.BNPair.BuildingsFromBNPairs.Part5
set_option linter.unusedSectionVars false

variable {B_idx : Type*} [DecidableEq B_idx]


namespace BNPair

variable {G : Type*} [Group G] {M : CoxeterMatrix B_idx}

/-- Defining property of the chosen representatives: $S' \neq S$ and $Q$ equals the conjugate parabolic. -/
theorem properParabolicRepr_prop (bp : BNPair G M) (Q : bp.properParabolics) :
    bp.properParabolicReprS Q ≠ Set.univ ∧
    (Q : Set G) = bp.conjugateParabolic (bp.properParabolicReprG Q) (bp.properParabolicReprS Q) :=
  (Classical.choose_spec (Classical.choose_spec Q.prop)).imp_right id

/-- $Q$ equals the conjugate parabolic $g P_{S'} g^{-1}$ formed from the chosen representatives. -/
theorem properParabolicRepr_eq (bp : BNPair G M) (Q : bp.properParabolics) :
    (Q : Set G) = bp.conjugateParabolic (bp.properParabolicReprG Q) (bp.properParabolicReprS Q) :=
  (properParabolicRepr_prop bp Q).2

end BNPair
