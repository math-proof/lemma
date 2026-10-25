/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part6
import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.KingSegmentDownClose
import Theorem.StatisticalMechanics.Code.Lattice.KingDescentAgnosticClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.KingStepConnectClose
import Theorem.StatisticalMechanics.Code.Lattice.KingNoSeparationClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EscapeThickPointClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EscapeWallThickClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GlobalThickPointClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossArcThickClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingPinchClose
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsCycleClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

noncomputable def pcy_fig8_A : (hypercubicLattice 2).Walk ![(2:ℤ),2] ![(2:ℤ),2] :=
  let a1 : (hypercubicLattice 2).Walk ![(2:ℤ),2] ![0,2] :=
    ((jec_hsegRight 2 0 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let a2 : (hypercubicLattice 2).Walk ![(0:ℤ),2] ![0,0] :=
    ((jec_vsegUp 0 0 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let a3 : (hypercubicLattice 2).Walk ![(0:ℤ),0] ![2,0] :=
    (jec_hsegRight 0 0 2).copy rfl (by ext i; fin_cases i <;> simp)
  let a4 : (hypercubicLattice 2).Walk ![(2:ℤ),0] ![2,2] :=
    (jec_vsegUp 2 0 2).copy rfl (by ext i; fin_cases i <;> simp)
  a1.append (a2.append (a3.append a4))


noncomputable def pcy_fig8_B : (hypercubicLattice 2).Walk ![(2:ℤ),2] ![(2:ℤ),2] :=
  let b1 : (hypercubicLattice 2).Walk ![(2:ℤ),2] ![4,2] :=
    (jec_hsegRight 2 2 2).copy rfl (by ext i; fin_cases i <;> simp)
  let b2 : (hypercubicLattice 2).Walk ![(4:ℤ),2] ![4,4] :=
    (jec_vsegUp 4 2 2).copy rfl (by ext i; fin_cases i <;> simp)
  let b3 : (hypercubicLattice 2).Walk ![(4:ℤ),4] ![2,4] :=
    ((jec_hsegRight 4 2 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let b4 : (hypercubicLattice 2).Walk ![(2:ℤ),4] ![2,2] :=
    ((jec_vsegUp 2 2 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  b1.append (b2.append (b3.append b4))


end Lattice
end StatMech
