/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcededgeopen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bkm_dccstepopen
import Theorem.StatisticalMechanics.Code.Walls.bc_wiringforcesopen
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
open Set
open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc2_forced_edge_open_eq_true (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) {u v : Site d}
    (hmem : s(u, v) ∈ W) (h0 : (0 : Site d) ∉ s(u, v)) :
    removeSite 0 (forceOpenFinset W ω) s(u, v) = true :=
  bkm_dcc_step_open_eq_true ω W hmem h0


theorem bc2_forced_edge_open (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) {u v : Site d}
    (hadj : (hypercubicLattice d).Adj u v)
    (hmem : s(u, v) ∈ W) (h0 : (0 : Site d) ∉ s(u, v)) :
    IsOpenEdge d (removeSite 0 (forceOpenFinset W ω)) u v :=
  bkm_dcc_step_open ω W hadj hmem h0


theorem bc2_forced_edge_open_mem (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) {e : Sym2 (Site d)}
    (hmem : e ∈ W) (h0 : (0 : Site d) ∉ e) :
    removeSite 0 (forceOpenFinset W ω) e = true := by
  induction e using Sym2.ind with
  | _ u v => exact bc2_forced_edge_open_eq_true ω W hmem h0


end Walls
end StatMech
