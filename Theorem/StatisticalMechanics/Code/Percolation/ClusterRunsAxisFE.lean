/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterRunsAxisFE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.MengerCorridors.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem craf_mem_corridorEdges (j : Fin d) (L : ℕ) {t : ℕ} (ht : t < L) :
    s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) ∈ hrHD_corridorEdges j (L + 1) := by
  have hmem := hrHD_mem_corridorEdges (j := j) (L := L + 1) (t := t + 1) (by omega)
  have e1 : (((t : ℕ) + 1 : ℕ) : ℤ) = (t : ℤ) + 1 := by push_cast; ring
  rw [e1] at hmem
  have e2 : ((t : ℤ) + 1 + 1) = (t : ℤ) + 2 := by ring
  rwa [e2] at hmem


theorem craf_corridor_axis_edge_open (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    {t : ℕ} (ht : t < L) :
    forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω
      s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true :=
  forceOpenFinset_of_mem (craf_mem_corridorEdges j L ht) ω


end Percolation
end StatMech
