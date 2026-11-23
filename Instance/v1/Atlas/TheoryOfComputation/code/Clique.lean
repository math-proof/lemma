/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.NPCompleteness
public import Def.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part8
public import Def.v1.Atlas.TheoryOfComputation.code.Clique.Part2
@[expose] public section

namespace ThreeSATToClique

/-- Contradictoriness of literals is decidable, inherited from decidability of
equality on variable indices and polarities. -/
instance (l₁ l₂ : Literal) : Decidable (l₁.IsContradictory l₂) :=
  inferInstanceAs (Decidable (_ ∧ _))

end ThreeSATToClique
