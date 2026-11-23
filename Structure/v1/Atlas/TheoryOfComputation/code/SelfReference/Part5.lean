/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
public import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part13
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.Decidability
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.Set
public import Def.v1.Atlas.TheoryOfComputation.code.SelfReference.Part5


public section

namespace TuringMachine

open TuringMachine

/-- A `TMCoding` augmented with a computable "complement" operation `compl`
mapping each index `M` to an index whose language is the set complement of
`L(M)`. Useful for applying the Recursion Theorem to constructions that flip
acceptance. -/
structure TMCodingWithCompl (Γ : Type) where
  coding : TMCoding Γ
  compl : coding.TMIndex → coding.TMIndex
  compl_spec : ∀ M : coding.TMIndex, coding.languageOf (compl M) = (coding.languageOf M)ᶜ
  compl_computable : coding.IsComputable compl

end TuringMachine
