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
import Instance.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part3


namespace CookLevin

open TuringMachine NPCompleteness

/-- An NTM that decides `HampathLang` in one step: accepts iff the (nonblank) input
symbol encodes a YES instance of HAMPATH. -/
noncomputable def hampathNTM : NTM HampathState HampathSymbol where
  blank := HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩
  inputAlpha := {x | x ≠ HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩}
  blank_not_in_inputAlpha := by simp
  q₀ := .start
  qAccept := .accept
  qReject := .reject
  qReject_ne_qAccept := by decide
  δ := fun q γ => by classical exact
    match q with
    | .start =>
      if γ ≠ HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩ ∧ γ.isYesInstance
      then {(.accept, γ, Direction.R)}
      else {(.reject, γ, Direction.R)}
    | .accept => ∅
    | .reject => ∅

end CookLevin
