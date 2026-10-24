/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter11/Containers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option maxHeartbeats 400000

namespace ContainersTriangleFree

open SimpleGraph Classical

/-- **Theorem 11.1.1 (Containers for triangle-free graphs).** For every $\varepsilon > 0$,
there is a constant $C > 0$ such that for every $n$ there is a family $\mathcal{C}$ of
graphs on $[n]$ with:
* $|\mathcal{C}| \leq n^{C n^{3/2}}$;
* every $G \in \mathcal{C}$ has at most $(1/4 + \varepsilon) n^2$ edges;
* every triangle-free graph on $[n]$ is contained in some $G \in \mathcal{C}$. -/
end ContainersTriangleFree
