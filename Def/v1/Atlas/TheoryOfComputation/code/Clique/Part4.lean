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
import Abbrev.v1.Atlas.TheoryOfComputation.code.Clique


namespace ThreeSATToClique

/-- Project the `j`-th literal (for `j : Fin 3`) out of a 3-clause. -/
def ThreeClause.literalAt (c : ThreeClause) (j : Fin 3) : Literal :=
  match j with
  | ⟨0, _⟩ => c.1
  | ⟨1, _⟩ => c.2.1
  | ⟨2, _⟩ => c.2.2

/-- A 3-clause is satisfied by an assignment `σ` iff at least one of its three
literals evaluates to `true` under `σ`. -/
def ThreeClause.isSatBy (σ : ℕ → Bool) (c : ThreeClause) : Prop :=
  ∃ j : Fin 3, (c.literalAt j).eval σ = true

end ThreeSATToClique
