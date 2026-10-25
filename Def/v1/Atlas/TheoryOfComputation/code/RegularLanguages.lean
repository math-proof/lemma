/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularLanguages.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Powerset
import Abbrev.v1.Atlas.TheoryOfComputation.code.RegularLanguages
open Computability


namespace DFA

variable {α : Type*} {σ : Type*}

/-- The language recognized by a DFA `M`: the set of strings `M` accepts. -/
def language (M : DFA α σ) : Language α :=
  M.accepts

end DFA

namespace RegularLanguages

/-- A language `L` is **regular** if some finite automaton recognizes it.

Equivalent to Mathlib's `Language.IsRegular`. This matches Sipser's
definition: `L` is regular iff `L = L(M)` for some DFA `M`. -/
def IsRegular {α : Type*} (L : Language α) : Prop :=
  L.IsRegular

/-- Concatenation of two languages: `A · B = { ab | a ∈ A, b ∈ B }`,
realized in Mathlib as `A * B`. -/
def concat {α : Type*} (A B : Language α) : Language α := A * B

end RegularLanguages
