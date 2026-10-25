/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LogSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Ring
import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Structure.v1.Atlas.TheoryOfComputation.code.LogSpace
open SpaceComplexity
open TuringMachine


namespace LogSpace

/-- The type of log-space configurations restricted so that the input head lies
in `Fin n`, the work head lies in `Fin s`, and the work tape is encoded as a
function `Fin s → Γ`. This is a finite type whenever `Q` and `Γ` are. -/
def BoundedLogSpaceConfig (Q : Type) (Γ : Type) (n s : ℕ) :=
  Q × Fin n × Fin s × (Fin s → Γ)

end LogSpace
