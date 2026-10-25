/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Nodup
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Structure.v1.Atlas.TheoryOfComputation.code.Tableau
import Instance.v1.Atlas.TheoryOfComputation.code.NPCompleteness


namespace CookLevin

open TuringMachine NPCompleteness

/--
An NTM that decides `SATLang` "nondeterministically in one step": on input `[φ]`,
it goes to accept iff φ is satisfiable, otherwise to reject. This witnesses that
SAT ∈ NP using the alphabet `BoolFormula` (one symbol per formula).
-/
noncomputable def satNTM : NTM SATState BoolFormula where
  blank := .falseConst
  inputAlpha := {x | x ≠ .falseConst}
  blank_not_in_inputAlpha := by simp
  q₀ := .start
  qAccept := .accept
  qReject := .reject
  qReject_ne_qAccept := by decide
  δ := fun q γ => by classical exact
    match q with
    | .start =>
      if γ ≠ .falseConst ∧ γ.Satisfiable then {(.accept, γ, Direction.R)}
      else {(.reject, γ, Direction.R)}
    | .goodHead => {(.reject, γ, Direction.R)}
    | .badHead => {(.reject, γ, Direction.R)}
    | .accept => ∅
    | .reject => ∅

/-- The 3SAT language presented as singleton-list inputs: `[φ]` belongs iff `φ`
is a satisfiable 3CNF formula. -/
def ThreeSATLang : Set (List BoolFormula) :=
  {w | ∃ φ : BoolFormula, w = [φ] ∧ φ.Is3CNF ∧ φ.Satisfiable}

end CookLevin
