/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.Exploration.Part4
open MeasureTheory Function Set
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


variable {d : ℕ}


theorem clusterEvent_congr {S : Set (Site d)} {o : Site d} {K : Set (Site d)} (hoS : o ∈ S)
    {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hagree : ∀ e ∈ incidentWithin K S, ω e = ω' e)
    (hω : ω ∈ clusterEvent d S o K) : ω' ∈ clusterEvent d S o K := by
  have hK : clusterWithin d ω S o = K := hω
  have hagree' : ∀ e ∈ incidentWithin (clusterWithin d ω S o) S, ω e = ω' e := by
    rw [hK]; exact hagree
  show clusterWithin d ω' S o = K
  rw [clusterWithin_congr hoS hagree', hK]

theorem clusterEvent_iff {S : Set (Site d)} {o : Site d} {K : Set (Site d)} (hoS : o ∈ S)
    {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hagree : ∀ e ∈ incidentWithin K S, ω e = ω' e) :
    ω ∈ clusterEvent d S o K ↔ ω' ∈ clusterEvent d S o K :=
  ⟨clusterEvent_congr hoS hagree,
   clusterEvent_congr hoS (fun e he => (hagree e he).symm)⟩


end Percolation
end StatMech
