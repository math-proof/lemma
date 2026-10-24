/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/ChromaticConcentration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Combinatorics.SimpleGraph.Coloring
set_option maxHeartbeats 400000

open MeasureTheory Measure SimpleGraph Real

namespace ChromaticConcentration

/-- Two graphs $G$ and $G'$ on vertex set $V$ differ only at vertex $v$: their adjacency
relations agree on all pairs not involving $v$. -/
def DiffOnlyAt {V : Type*} (G G' : SimpleGraph V) (v : V) : Prop :=
  ∀ a b, a ≠ v → b ≠ v → (G.Adj a b ↔ G'.Adj a b)

/-- The chromatic number of a graph on `Fin n`, viewed as a real number. -/
noncomputable def chromaticNumberReal (n : ℕ) (G : SimpleGraph (Fin n)) : ℝ :=
  (G.chromaticNumber.toNat : ℝ)


/-- Upper-tail bounded differences inequality applied to the chromatic number of $G(n,p)$:
$\mathbb{P}(\chi(G) - \mathbb{E}\chi(G) \geq \varepsilon) \leq \exp(-2\varepsilon^2/(n-1))$. -/
end ChromaticConcentration
