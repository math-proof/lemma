/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter8/ChromaticNumber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.ChromaticNumber
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.ChromaticNumber
set_option maxHeartbeats 400000

/-- Property $\star$ for $G(n, 1/2)$ holds with high probability: for every $\varepsilon > 0$
and all large $n$, the probability that $G(n,1/2)$ contains a subset $S$ of size
$\geq n / (\log_2 n)^2$ none of whose $(k_0 - 3)$-subsets is independent is at most
$\exp(-n^{1-\varepsilon})$. -/


namespace ChromaticRandom

open SimpleGraph Finset

end ChromaticRandom
