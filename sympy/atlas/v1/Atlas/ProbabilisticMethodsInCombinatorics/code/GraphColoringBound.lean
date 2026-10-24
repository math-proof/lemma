/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/GraphColoringBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

namespace GraphColoringBound


/-- Theorem 10.4.15 (Sah–Sawhney–Stoner–Zhao 2020). For every $d$-regular graph $G$ on
$n$ vertices and every $q \ge 1$, the number $c_q(G)$ of proper $q$-colourings satisfies
$c_q(G) \le c_q(K_{d,d})^{n/(2d)}$. -/
end GraphColoringBound
