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
import Def.StatisticalMechanics.Code.Universality.G3PercDefs
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim

variable {d : ℕ}


theorem g3OriginCluster_eq (ω : ConfigSpace (Sym2 (Site d))) :
    g3OriginCluster d ω = originCluster d ω := rfl


theorem origin_mem_g3OriginCluster (ω : ConfigSpace (Sym2 (Site d))) :
    (0 : Site d) ∈ g3OriginCluster d ω :=
  origin_mem_originCluster ω


theorem g3OriginCluster_mono {ω ω' : ConfigSpace (Sym2 (Site d))} (h : ω ≤ ω') :
    g3OriginCluster d ω ⊆ g3OriginCluster d ω' :=
  originCluster_mono h


end Universality
end StatMech
