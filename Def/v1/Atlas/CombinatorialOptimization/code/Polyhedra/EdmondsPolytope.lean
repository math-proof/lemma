/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Polyhedra/EdmondsPolytope.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open SimpleGraph Finset BigOperators Classical


noncomputable section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def incidentEdgeFinset (v : V) : Finset G.edgeSet :=
  (G.edgeFinset.filter (fun e => v ∈ e)).subtype (fun e => e ∈ G.edgeSet)

def edgeCutFinset (S : Finset V) : Finset G.edgeSet :=
  (G.edgeFinset.filter (fun e =>
    ∃ a ∈ S, ∃ b ∉ S, e = s(a, b))).subtype (fun e => e ∈ G.edgeSet)

def perfectMatchingIndicators : Set (G.edgeSet → ℝ) :=
  {x | ∃ (M : G.Subgraph) (_ : M.IsPerfectMatching),
    x = fun (e : G.edgeSet) => if (e : Sym2 V) ∈ M.edgeSet then (1 : ℝ) else 0}

def perfectMatchingPolytope : Set (G.edgeSet → ℝ) :=
  (convexHull ℝ) (perfectMatchingIndicators G)

def edmondsPolytope : Set (G.edgeSet → ℝ) :=
  {x | (∀ e : G.edgeSet, 0 ≤ x e) ∧
       (∀ v : V, ∑ e ∈ incidentEdgeFinset G v, x e = 1) ∧
       (∀ S : Finset V, Odd S.card →
         ∑ e ∈ edgeCutFinset G S, x e ≥ 1)}

end SimpleGraph
end
