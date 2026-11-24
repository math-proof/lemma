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
public import Def.v1.Atlas.TheoryOfComputation.code.LogSpace.Part2
open SpaceComplexity
open TuringMachine


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LogSpace.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace LogSpace

/-- `BoundedLogSpaceConfig Q Γ n s` is a finite type, inherited from the
product structure of its components. -/
noncomputable instance BoundedLogSpaceConfig.fintype
    (Q : Type) (Γ : Type) [Fintype Q] [Fintype Γ] (n s : ℕ) :
    Fintype (BoundedLogSpaceConfig Q Γ n s) :=
  inferInstanceAs (Fintype (Q × Fin n × Fin s × (Fin s → Γ)))

end LogSpace
