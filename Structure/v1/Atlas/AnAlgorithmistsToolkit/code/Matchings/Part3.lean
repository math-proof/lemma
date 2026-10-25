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
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.Matchings.Part2
open Finset


namespace Matchings

attribute [instance] BipartiteGraph.decAdj

namespace PartialMatching

variable {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G)

structure SizedMatching {n : ℕ} (G : BipartiteGraph n) (k : ℕ) where
  edges : Finset (Fin n × Fin n)
  edge_adj : ∀ p ∈ edges, G.Adj p.1 p.2
  left_inj : ∀ ⦃p q⦄, p ∈ edges → q ∈ edges → p.1 = q.1 → p = q
  right_inj : ∀ ⦃p q⦄, p ∈ edges → q ∈ edges → p.2 = q.2 → p = q
  card_eq : edges.card = k

end PartialMatching
end Matchings
