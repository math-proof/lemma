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


namespace SelfReference

open TuringMachine

/-- A self-contained description of a Turing machine over the tape alphabet `Γ`.
Bundles the (existential) state type `Q`, its `DecidableEq` instance, the underlying
`TM`, and an optional explicit source/encoding `source : List Γ` used by certain
concrete encodings. -/
structure TMDescription (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  machine : TM Q Γ
  source : List Γ := []

end SelfReference
