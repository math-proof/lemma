/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/SidorenkoCompleteBipartite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace SidorenkoCompleteBipartite

open SimpleGraph Finset BigOperators

/-- Homomorphism count $\mathrm{hom}(K_{s,t}, G)$ from the complete bipartite graph
$K_{s,t}$ into $G$: choose an $s$-tuple $\mathbf{x}$ in $V(G)$, then count its common
neighborhood and raise to the power $t$. -/
noncomputable def homCountBip {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (s t : ℕ) : ℕ :=
  ∑ xs : Fin s → W,
    ((Finset.univ.filter fun y => ∀ i : Fin s, G.Adj (xs i) y).card) ^ t
