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
import Instance.v1.Atlas.TheoryOfComputation.code.Clique


namespace ThreeSATToClique

/-- Evaluate a literal under a truth assignment `σ : ℕ → Bool`: a positive
literal returns `σ l.varIdx`, a negative literal returns its negation. -/
def Literal.eval (σ : ℕ → Bool) (l : Literal) : Bool :=
  match l.pol with
  | .pos => σ l.varIdx
  | .neg => !σ l.varIdx

end ThreeSATToClique
