/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.KingInteriorFloodClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.KingSegmentDownClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

noncomputable def kda_stairDR : (hypercubicLattice 2).Walk ![(0:ℤ),(1:ℤ)] ![(0:ℤ),(1:ℤ)] :=
  let s1 : (hypercubicLattice 2).Walk ![(0:ℤ),1] ![0,3] :=
    (jec_vsegUp 0 1 2).copy rfl (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![(0:ℤ),3] ![3,3] :=
    (jec_hsegRight 3 0 3).copy rfl (by ext i; fin_cases i <;> simp)
  let s3 : (hypercubicLattice 2).Walk ![(3:ℤ),3] ![3,2] :=
    ((jec_vsegUp 3 2 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s4 : (hypercubicLattice 2).Walk ![(3:ℤ),2] ![4,2] :=
    (jec_hsegRight 2 3 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s5 : (hypercubicLattice 2).Walk ![(4:ℤ),2] ![4,0] :=
    ((jec_vsegUp 4 0 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s6 : (hypercubicLattice 2).Walk ![(4:ℤ),0] ![2,0] :=
    ((jec_hsegRight 0 2 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s7 : (hypercubicLattice 2).Walk ![(2:ℤ),0] ![2,1] :=
    (jec_vsegUp 2 0 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s8 : (hypercubicLattice 2).Walk ![(2:ℤ),1] ![0,1] :=
    ((jec_hsegRight 1 0 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  s1.append (s2.append (s3.append (s4.append (s5.append (s6.append (s7.append s8))))))


end Lattice
end StatMech
