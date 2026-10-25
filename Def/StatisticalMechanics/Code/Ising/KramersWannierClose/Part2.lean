/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section Matching

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


def CutEvenSubgraphMatching (t mult : ℝ) : Prop :=
  (∑ s : ConfigSpace V, t ^ (cutEdges Gp s).card)
    = mult * ∑ F ∈ Gd.edgeFinset.powerset.filter IsEvenSubgraph, t ^ F.card


end Matching
end Ising
end StatMech
