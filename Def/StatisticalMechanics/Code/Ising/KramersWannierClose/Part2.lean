module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
public import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
public import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose
open scoped BigOperators
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
