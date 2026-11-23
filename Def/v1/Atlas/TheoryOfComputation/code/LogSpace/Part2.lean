/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LogSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Ring
public import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Structure.v1.Atlas.TheoryOfComputation.code.LogSpace

@[expose] public section

open SpaceComplexity
open TuringMachine


namespace LogSpace

/-- The type of log-space configurations restricted so that the input head lies
in `Fin n`, the work head lies in `Fin s`, and the work tape is encoded as a
function `Fin s → Γ`. This is a finite type whenever `Q` and `Γ` are. -/
def BoundedLogSpaceConfig (Q : Type) (Γ : Type) (n s : ℕ) :=
  Q × Fin n × Fin s × (Fin s → Γ)

end LogSpace
