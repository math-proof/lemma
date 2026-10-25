/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Def.StatisticalMechanics.Code.Universality.G3PercDefs.Part2
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim

variable {d : ℕ}


theorem g3PercolationEvent_eq : g3PercolationEvent d = percolationEvent d := rfl

theorem mem_g3PercolationEvent {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ g3PercolationEvent d ↔ (g3OriginCluster d ω).Infinite := Iff.rfl


theorem g3PercolationEvent_increasing : IsIncreasing (g3PercolationEvent d) :=
  percolationEvent_increasing


end Universality
end StatMech
