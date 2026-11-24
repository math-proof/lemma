module
public import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
public import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
public import Theorem.Nat.NonemptyBruhatCell
public import Theorem.Set.All_In_StandardParabolic
public import Theorem.Nat.B.le.Closure_BruhatCell
public import Theorem.v1.Atlas.Buildings.code.BNPair.ConjugatorProof
public import Def.v1.Atlas.Buildings.code.BNPair.NormalizerParabolicProof
public import Mathlib.Tactic.Group
public import Theorem.v1.Atlas.Buildings.code.BNPair.BuildingsFromBNPairs.Part4
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

/-- Choose a conjugator $g$ such that $Q = g P_{S'} g^{-1}$ for a proper parabolic $Q$. -/
noncomputable def properParabolicReprG (bp : BNPair G M)
    (Q : bp.properParabolics) : G :=
  Classical.choose Q.prop

/-- Choose the parabolic type $S'$ such that $Q = g P_{S'} g^{-1}$ for a proper parabolic $Q$. -/
noncomputable def properParabolicReprS (bp : BNPair G M)
    (Q : bp.properParabolics) : Set B_idx :=
  Classical.choose (Classical.choose_spec Q.prop)

end BNPair
