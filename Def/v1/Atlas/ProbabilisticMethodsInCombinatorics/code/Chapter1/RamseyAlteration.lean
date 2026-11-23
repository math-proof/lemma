/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/RamseyAlteration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.RamseyLowerBound
public import Theorem.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter1.RamseyLowerBound

@[expose] public section

namespace RamseyAlteration

open Finset Fintype RamseyLowerBound

/-- The alteration bound: expected number of monochromatic $k$-cliques in a uniformly
random 2-coloring of $K_n$, namely $\binom{n}{k} \cdot 2 / 2^{\binom{k}{2}}$. -/
def alterationBound (n k : ℕ) : ℕ := n.choose k * 2 / 2 ^ k.choose 2

end RamseyAlteration
