/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Walls.jcwcutsetwalk
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Theorem.StatisticalMechanics.Code.Ising.DualWalkBoundsClose.Part3
import Theorem.StatisticalMechanics.Code.Walls.kwffaceclose.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising

attribute [local instance] Classical.propDecidable


noncomputable def kwf_rightSquare :
    (hypercubicLattice 2).Walk ![1, 1] ![1, 1] :=
  let s1 : (hypercubicLattice 2).Walk ![1, 1] ![2, 1] :=
    (jec_hsegRight 1 1 1).copy (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![2, 1] ![2, 2] :=
    (jec_vsegUp 2 1 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s3 : (hypercubicLattice 2).Walk ![2, 2] ![1, 2] :=
    ((jec_hsegRight 2 1 1).copy (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp)).reverse
  let s4 : (hypercubicLattice 2).Walk ![1, 2] ![1, 1] :=
    ((jec_vsegUp 1 1 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  s1.append (s2.append (s3.append s4))


end Walls
end StatMech
