/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Def.StatisticalMechanics.Code.Universality.Defs
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


variable {d : ℕ}


@[simp]
theorem mem_originCluster {ω : ConfigSpace (Sym2 (Site d))} {y : Site d} :
    y ∈ originCluster d ω ↔ Connected d ω (0 : Site d) y := Iff.rfl


theorem origin_mem_originCluster (ω : ConfigSpace (Sym2 (Site d))) :
    (0 : Site d) ∈ originCluster d ω :=
  self_mem_cluster ω (0 : Site d)


theorem originCluster_mono {ω ω' : ConfigSpace (Sym2 (Site d))} (h : ω ≤ ω') :
    originCluster d ω ⊆ originCluster d ω' :=
  cluster_mono_dim h (0 : Site d)


end Universality
end StatMech
