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
import Inductive.v1.Atlas.TheoryOfComputation.code.Clique.Part2


namespace ThreeSATToClique

/-- Encoded 3SAT language: those single-symbol tape strings `[.sat φ]` whose
underlying formula `φ` is satisfiable. -/
def ThreeSATEnc : Set (List SATCliqueSymbol) :=
  {w | ∃ φ : ThreeCNF, w = [.sat φ] ∧ φ.IsSatisfiable}

/-- Encoded CLIQUE language (specialized to instances arising from the
reduction): the single-symbol strings `[.clique φ]` whose reduction graph
`reductionGraph φ` contains a `|φ|`-clique. -/
def CLIQUEEnc : Set (List SATCliqueSymbol) :=
  {w | ∃ (φ : ThreeCNF),
    w = [.clique φ] ∧ Clique.HasKClique (reductionGraph φ) φ.length}

/-- The reduction function `f : Σ* → Σ*` on encodings: maps `[.sat φ]` to
`[.clique φ]` and every other input to the empty string. -/
def threeSATToCliqueEnc : List SATCliqueSymbol → List SATCliqueSymbol
  | [.sat φ] => [.clique φ]
  | _ => []

end ThreeSATToClique
