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
import Def.v1.Atlas.TheoryOfComputation.code.Clique.Part5


namespace ThreeSATToClique

/-- Tape alphabet used to encode either a 3SAT instance or a CLIQUE instance
on a single Turing-machine tape. The symbol `sat φ` represents an encoded
3CNF formula `φ`, and `clique φ` represents the encoded CLIQUE instance
`⟨reductionGraph φ, |φ|⟩`. -/
inductive SATCliqueSymbol where
  | sat (φ : ThreeCNF) : SATCliqueSymbol
  | clique (φ : ThreeCNF) : SATCliqueSymbol

end ThreeSATToClique
