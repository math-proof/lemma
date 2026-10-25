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


namespace Clique

open SimpleGraph

/-- A graph `G` has a `k`-clique iff there exists a `k`-vertex subset all of
whose pairs are adjacent in `G`. -/
def HasKClique {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (s : Finset V), G.IsNClique k s

/-- The language `CLIQUE = {⟨G, k⟩ | G has a k-clique}` as a set of
graph/integer pairs. -/
def CLIQUE (V : Type*) : Set (SimpleGraph V × ℕ) :=
  {p | HasKClique p.1 p.2}

end Clique
