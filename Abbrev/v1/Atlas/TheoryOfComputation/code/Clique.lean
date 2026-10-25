/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.NPCompleteness
import Def.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part8
import Def.v1.Atlas.TheoryOfComputation.code.Clique.Part3


namespace ThreeSATToClique

/-- A 3-clause is a triple of literals, representing the disjunction
`l₁ ∨ l₂ ∨ l₃` in a 3CNF formula. -/
abbrev ThreeClause := Literal × Literal × Literal

end ThreeSATToClique
