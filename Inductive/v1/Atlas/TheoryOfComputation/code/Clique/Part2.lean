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
public import Def.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part8
public import Def.v1.Atlas.TheoryOfComputation.code.Clique.Part5

namespace ThreeSATToClique

/-- Tape alphabet used to encode either a 3SAT instance or a CLIQUE instance
on a single Turing-machine tape. The symbol `sat φ` represents an encoded
3CNF formula `φ`, and `clique φ` represents the encoded CLIQUE instance
`⟨reductionGraph φ, |φ|⟩`. -/
public inductive SATCliqueSymbol where
  | sat (φ : ThreeCNF) : SATCliqueSymbol
  | clique (φ : ThreeCNF) : SATCliqueSymbol

end ThreeSATToClique
