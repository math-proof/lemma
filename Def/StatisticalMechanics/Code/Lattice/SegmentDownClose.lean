/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

noncomputable def sdc_fjord : (hypercubicLattice 2).Walk ![(0:ℤ),(0:ℤ)] ![(0:ℤ),(0:ℤ)] :=
  let s1 : (hypercubicLattice 2).Walk ![(0:ℤ),0] ![3,0] :=
    (jec_hsegRight 0 0 3).copy rfl (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![(3:ℤ),0] ![3,3] :=
    (jec_vsegUp 3 0 3).copy rfl (by ext i; fin_cases i <;> simp)
  let s3 : (hypercubicLattice 2).Walk ![(3:ℤ),3] ![4,3] :=
    (jec_hsegRight 3 3 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s4 : (hypercubicLattice 2).Walk ![(4:ℤ),3] ![4,0] :=
    ((jec_vsegUp 4 0 3).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s5 : (hypercubicLattice 2).Walk ![(4:ℤ),0] ![7,0] :=
    (jec_hsegRight 0 4 3).copy rfl (by ext i; fin_cases i <;> simp)
  let s6 : (hypercubicLattice 2).Walk ![(7:ℤ),0] ![7,4] :=
    (jec_vsegUp 7 0 4).copy rfl (by ext i; fin_cases i <;> simp)
  let s7 : (hypercubicLattice 2).Walk ![(7:ℤ),4] ![0,4] :=
    ((jec_hsegRight 4 0 7).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s8 : (hypercubicLattice 2).Walk ![(0:ℤ),4] ![0,0] :=
    ((jec_vsegUp 0 0 4).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  s1.append (s2.append (s3.append (s4.append (s5.append (s6.append (s7.append s8))))))


end Lattice
end StatMech
