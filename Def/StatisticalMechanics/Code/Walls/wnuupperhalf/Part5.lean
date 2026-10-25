/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part4
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

noncomputable def wnu_LtrominoLoop : (hypercubicLattice 2).Walk ![0, 0] ![0, 0] :=
  let a : (hypercubicLattice 2).Walk ![0, 0] ![2, 0] :=
    (jec_hsegRight 0 0 2).copy rfl (by ext i; fin_cases i <;> simp)
  let b : (hypercubicLattice 2).Walk ![2, 0] ![2, 1] :=
    (jec_vsegUp 2 0 1).copy rfl (by ext i; fin_cases i <;> simp)
  let c : (hypercubicLattice 2).Walk ![2, 1] ![1, 1] :=
    ((jec_hsegRight 1 1 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let d : (hypercubicLattice 2).Walk ![1, 1] ![1, 2] :=
    (jec_vsegUp 1 1 1).copy rfl (by ext i; fin_cases i <;> simp)
  let e : (hypercubicLattice 2).Walk ![1, 2] ![0, 2] :=
    ((jec_hsegRight 2 0 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let f : (hypercubicLattice 2).Walk ![0, 2] ![0, 0] :=
    ((jec_vsegUp 0 0 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  a.append (b.append (c.append (d.append (e.append f))))


end Lattice
end StatMech
