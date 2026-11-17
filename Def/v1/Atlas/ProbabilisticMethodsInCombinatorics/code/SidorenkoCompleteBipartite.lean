/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/SidorenkoCompleteBipartite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace SidorenkoCompleteBipartite

open SimpleGraph Finset BigOperators

/-- Homomorphism count $\mathrm{hom}(K_{s,t}, G)$ from the complete bipartite graph
$K_{s,t}$ into $G$: choose an $s$-tuple $\mathbf{x}$ in $V(G)$, then count its common
neighborhood and raise to the power $t$. -/
noncomputable def homCountBip {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (s t : ℕ) : ℕ :=
  ∑ xs : Fin s → W,
    ((Finset.univ.filter fun y => ∀ i : Fin s, G.Adj (xs i) y).card) ^ t

end SidorenkoCompleteBipartite
