/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/GalvinTetali.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public section

set_option maxHeartbeats 400000


namespace GalvinTetali

open scoped Classical

/-- A `LoopGraph` on a vertex set $W$: a symmetric relation `Adj` on $W$, allowing
self-loops (unlike `SimpleGraph`). Used as the target graph $H$ in graph homomorphism
counts. -/
structure LoopGraph (W : Type*) where
  Adj : W → W → Prop
  symm : ∀ u v, Adj u v → Adj v u

end GalvinTetali
