/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part5
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box


def jec_vsegUp (col : ℤ) : (r : ℤ) → (k : ℕ) →
    (hypercubicLattice 2).Walk ![col, r] ![col, r + (k:ℤ)]
  | r, 0 => (SimpleGraph.Walk.nil).copy rfl (by norm_num)
  | r, (k+1) => by
      have hadj : (hypercubicLattice 2).Adj ![col, r] ![col, r+1] := by
        simp [hypercubicLattice_adj, Fin.sum_univ_two]
      exact (SimpleGraph.Walk.cons hadj (jec_vsegUp col (r+1) k)).copy rfl (by push_cast; ring_nf)


def jec_hsegRight (row : ℤ) : (t : ℤ) → (k : ℕ) →
    (hypercubicLattice 2).Walk ![t, row] ![t + (k:ℤ), row]
  | t, 0 => (SimpleGraph.Walk.nil).copy rfl (by norm_num)
  | t, (k+1) => by
      have hadj : (hypercubicLattice 2).Adj ![t, row] ![t+1, row] := by
        simp [hypercubicLattice_adj, Fin.sum_univ_two]
      exact (SimpleGraph.Walk.cons hadj (jec_hsegRight row (t+1) k)).copy rfl
        (by push_cast; ring_nf)


end Lattice
end StatMech
