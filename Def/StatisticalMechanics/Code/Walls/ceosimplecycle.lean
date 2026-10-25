/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ceosimplecycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
open Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice


noncomputable def ceo_shiftSquare : (hypercubicLattice 2).Walk ![0, 1] ![0, 1] :=
  let s1 : (hypercubicLattice 2).Walk ![0, 1] ![1, 1] :=
    (jec_hsegRight 1 0 1).copy (by ext i; fin_cases i <;> simp) (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![1, 1] ![1, 2] :=
    (jec_vsegUp 1 1 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s3 : (hypercubicLattice 2).Walk ![1, 2] ![0, 2] :=
    ((jec_hsegRight 2 0 1).copy (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp)).reverse
  let s4 : (hypercubicLattice 2).Walk ![0, 2] ![0, 1] :=
    ((jec_vsegUp 0 1 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  s1.append (s2.append (s3.append s4))


end Walls
end StatMech
