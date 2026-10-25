/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Roots
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation.Part4
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.DihedralPositivity
open Finset BigOperators


namespace CoxeterGroup

set_option linter.unusedSectionVars false

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Even-length alternating word $s\,t\,s\,t\,\cdots$ of length $2n$ starting
with $s$, defined recursively. -/
def altWordEven (s t : B) : ℕ → List B
  | 0 => []
  | n + 1 => s :: t :: altWordEven s t n

end CoxeterGroup
