/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanGenericCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanListSeries.Part2
import Theorem.StatisticalMechanics.Code.Onsager.ShermanReroot.Part4


namespace StatMech.Onsager

open Matrix BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

def ons_validRootedList (e r : E) (w : List E) : Prop :=
  w.head? = some e ∧ w.getLast? = some e ∧ ∀ x ∈ w, x ≠ r

def ons_validFactorList (e r : E) (ss : List (List E)) : Prop :=
  ∀ s ∈ ss, ons_isFirstReturnSegment e s ∧ ∀ x ∈ s, x ≠ r

end StatMech.Onsager
