/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorDodgeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorCoveredClose.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

noncomputable def edc_ring : (hypercubicLattice 2).Walk ![(1:ℤ),0] ![(1:ℤ),0] :=
  (Walk.cons (show (hypercubicLattice 2).Adj ![(1:ℤ),0] ![(1:ℤ),1] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  (Walk.cons (show (hypercubicLattice 2).Adj ![(1:ℤ),1] ![(0:ℤ),1] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  (Walk.cons (show (hypercubicLattice 2).Adj ![(0:ℤ),1] ![(-1:ℤ),1] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  (Walk.cons (show (hypercubicLattice 2).Adj ![(-1:ℤ),1] ![(-1:ℤ),0] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  (Walk.cons (show (hypercubicLattice 2).Adj ![(-1:ℤ),0] ![(-1:ℤ),-1] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  (Walk.cons (show (hypercubicLattice 2).Adj ![(-1:ℤ),-1] ![(0:ℤ),-1] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  (Walk.cons (show (hypercubicLattice 2).Adj ![(0:ℤ),-1] ![(1:ℤ),-1] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  (Walk.cons (show (hypercubicLattice 2).Adj ![(1:ℤ),-1] ![(1:ℤ),0] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  Walk.nil))))))))


noncomputable def edc_Vc : (hypercubicLattice 2).Walk ![(1:ℤ),0] ![(1:ℤ),0] :=
  edc_ring.append edc_ring.reverse


end Lattice
end StatMech
