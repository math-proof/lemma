/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter8/ChromaticNumber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.ChromaticNumber
public import Theorem.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.ChromaticNumber
set_option maxHeartbeats 400000

public section

/-- Property $\star$ for $G(n, 1/2)$ holds with high probability: for every $\varepsilon > 0$
and all large $n$, the probability that $G(n,1/2)$ contains a subset $S$ of size
$\geq n / (\log_2 n)^2$ none of whose $(k_0 - 3)$-subsets is independent is at most
$\exp(-n^{1-\varepsilon})$. -/


namespace ChromaticRandom

open SimpleGraph Finset

end ChromaticRandom
