/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
import Theorem.StatisticalMechanics.Code.Percolation.PcFarContour
import Theorem.StatisticalMechanics.Code.Percolation.OutermostContour
open Finset Set SimpleGraph Function


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


def outC_FarAxisHeadsFar (ω : ConfigSpace (Sym2 (Site 2)))
    (_hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  ∃ (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R),
    (![(R : ℤ) + 1, 0] : Site 2) ∈ exterior 2 R ∧
    (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R ∧
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨![(R : ℤ) + 1, 0], outC_axisFarRight_mem_compl R hR⟩
      ⟨![-((R : ℤ) + 1), 0], outC_axisFarLeft_mem_compl R hR⟩


end Percolation
end StatMech
