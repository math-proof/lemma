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
import Structure.v1.Atlas.AnAlgorithmistsToolkit.code.Matchings
open Finset


namespace Matchings

attribute [instance] BipartiteGraph.decAdj

namespace BipartiteGraph

variable {n : ℕ} (G : BipartiteGraph n)

instance (u : Fin n) (v : Fin n) : Decidable (G.Adj u v) :=
  G.decAdj (u, v)

end BipartiteGraph
end Matchings
