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
import Def.v1.Atlas.TheoryOfComputation.code.SelfReference.Part5


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
