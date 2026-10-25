/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part13
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Decidability
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Set
import Def.v1.Atlas.TheoryOfComputation.code.SelfReference.Part6


namespace TuringMachine

open TuringMachine

/-- A minimal abstract "formal proof system" over a TM-encoding `enc`. It picks
out a Turing-recognizable set `provable ⊆ Σ*` of provable statements about TM
descriptions, with the soundness assumption that if `⟨d⟩ ∈ provable` then `d`
does *not* accept (the statement "`d` is non-accepting" is true). -/
structure FormalProofSystem (Γ : Type) where
  enc : TMEncoding Γ
  provable : Set (List Γ)
  sound : ∀ (d : TMDesc Γ), enc.encode d ∈ provable → ¬d.accepts
  provable_recognizable : IsTuringRecognizable provable

end TuringMachine
