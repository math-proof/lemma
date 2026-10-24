/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/GraphContainers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.SimpleGraph
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Finset.Lattice.Fold
set_option maxHeartbeats 800000

open scoped Classical

open SimpleGraph Finset

namespace GraphContainers

variable {V W : Type*}

/-- `IsHFree G H` says that the graph $G$ contains no copy of $H$ as a subgraph. -/
def IsHFree (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  IsEmpty (H.Copy G)

/-- The finset of all $H$-free labelled graphs on the vertex set $\{1, \dots, n\}$. -/
noncomputable def hFreeGraphs (H : SimpleGraph W) (n : ℕ) : Finset (SimpleGraph (Fin n)) :=
  @Finset.filter _ (fun G => IsHFree G H) (Classical.decPred _) Finset.univ

/-- The extremal number $\mathrm{ex}(n, H)$: the maximum number of edges in an $H$-free
graph on $n$ vertices. -/
noncomputable def extremalNumber (H : SimpleGraph W) (n : ℕ) : ℕ :=
  (hFreeGraphs H n).sup fun G => G.edgeFinset.card

/-- Theorem 11.2.1 (Graph container theorem, non-bipartite case). For any non-bipartite
graph $H$ and every $\varepsilon > 0$, eventually the number of $H$-free graphs on
$n$ vertices is $2^{(1 \pm \varepsilon) \mathrm{ex}(n, H)}$. -/
noncomputable def averageDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)

/-- Container algorithm output. Given a graph $G$ with bounded max-to-average-degree
ratio and an independent set $I$, there exist a small fingerprint $\mathrm{fp} \subseteq I$
and an available set such that $I$ is contained in $\mathrm{fp} \cup \mathrm{avail}$, with
quantitative size bounds in terms of $\bar d(G)$. -/
def erdosRenyiMeasure (n : ℕ) (p : ℝ) :
    Measure (SimpleGraph (Fin n)) := by
  classical
  let m := (completeGraph (Fin n)).edgeFinset.card
  exact Measure.sum (fun G : SimpleGraph (Fin n) =>
    (ENNReal.ofReal (p ^ G.edgeFinset.card * (1 - p) ^ (m - G.edgeFinset.card))) •
      Measure.dirac G)

/-- The "bad" event in the random graph $G(n, p)$: there exists a triangle-free subgraph
$H \le G$ with more than `threshold` edges. -/
def badEvent (n : ℕ) (threshold : ℝ) : Set (SimpleGraph (Fin n)) := by
  classical
  exact {G | ∃ H : SimpleGraph (Fin n), H ≤ G ∧ H.CliqueFree 3 ∧
    (H.edgeFinset.card : ℝ) > threshold}
