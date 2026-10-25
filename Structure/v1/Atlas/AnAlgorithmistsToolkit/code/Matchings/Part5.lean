/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Matchings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.Convex.Birkhoff
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.Matchings.Part4
open Finset


namespace Matchings

attribute [instance] BipartiteGraph.decAdj

namespace PartialMatching

variable {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G)

structure TypeBPathData {n : ℕ} {G : BipartiteGraph n} (T : Transition G)
    (s t : PerfMatching G) where
  removed : Finset (Fin n × Fin n)
  added : Finset (Fin n × Fin n)
  removed_sub : removed ⊆ s.edges
  added_disj : Disjoint added s.edges
  removed_sub_symDiff : removed ⊆ s.edges \ t.edges
  added_sub_symDiff : added ⊆ t.edges \ s.edges
  encodingVertex : ChainVertex G
  encoding_edges_eq : chainVertexEdges encodingVertex = (s.edges \ removed) ∪ added
  canonRemoved : Finset (Fin n × Fin n)
  removed_eq_canon : removed = canonRemoved
  canonAdded : Finset (Fin n × Fin n)
  added_eq_canon : added = canonAdded
  canon_removed_spec : canonRemoved = chainVertexEdges T.source \ chainVertexEdges encodingVertex
  canon_added_spec : canonAdded = chainVertexEdges encodingVertex \ chainVertexEdges T.source
  canonSymDiff : Finset (Fin n × Fin n)
  symDiff_eq_canon : matchingSymDiff s t = canonSymDiff
  canon_symDiff_spec : canonSymDiff =
    (s.edges \ chainVertexEdges encodingVertex) ∪ (chainVertexEdges encodingVertex \ s.edges)

end PartialMatching
end Matchings
