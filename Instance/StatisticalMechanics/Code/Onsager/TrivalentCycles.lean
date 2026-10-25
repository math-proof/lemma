/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TrivalentCycles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CoeffMatch
import Def.StatisticalMechanics.Code.Onsager.TrivalentCycles


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

universe u

section

variable {V : Type u} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

instance ons_edgeSubgraph_decidableAdj (F : Finset (Sym2 V)) :
    DecidableRel (ons_edgeSubgraph F).Adj := by
  dsimp [ons_edgeSubgraph]
  infer_instance

end
end StatMech.Onsager
