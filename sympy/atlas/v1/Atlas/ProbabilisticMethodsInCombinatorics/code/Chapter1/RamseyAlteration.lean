/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/RamseyAlteration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.RamseyLowerBound
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter1.RamseyLowerBound

namespace RamseyAlteration

open Finset Fintype RamseyLowerBound

/-- The alteration bound: expected number of monochromatic $k$-cliques in a uniformly
random 2-coloring of $K_n$, namely $\binom{n}{k} \cdot 2 / 2^{\binom{k}{2}}$. -/
def alterationBound (n k : ℕ) : ℕ := n.choose k * 2 / 2 ^ k.choose 2
