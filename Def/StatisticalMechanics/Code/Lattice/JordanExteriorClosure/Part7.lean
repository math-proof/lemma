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
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part6
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box


def jec_retPath (α a0 b0 c d : ℤ) (_ha : α ≤ a0) (_hb : α ≤ b0) (_hcd : c ≤ d) :
    (hypercubicLattice 2).Walk ![b0, d] ![a0, c] :=
  let s1 : (hypercubicLattice 2).Walk ![b0, d] ![b0, d+1] :=
    (jec_vsegUp b0 d 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![b0, d+1] ![α-1, d+1] :=
    ((jec_hsegRight (d+1) (α-1) (b0-(α-1)).toNat).copy rfl
      (by ext i; fin_cases i <;> (simp; try omega))).reverse
  let s3 : (hypercubicLattice 2).Walk ![α-1, d+1] ![α-1, c-1] :=
    ((jec_vsegUp (α-1) (c-1) (d+1-(c-1)).toNat).copy rfl
      (by ext i; fin_cases i <;> (simp; try omega))).reverse
  let s4 : (hypercubicLattice 2).Walk ![α-1, c-1] ![a0, c-1] :=
    (jec_hsegRight (c-1) (α-1) (a0-(α-1)).toNat).copy rfl
      (by ext i; fin_cases i <;> (simp; try omega))
  let s5 : (hypercubicLattice 2).Walk ![a0, c-1] ![a0, c] :=
    (jec_vsegUp a0 (c-1) 1).copy rfl (by ext i; fin_cases i <;> simp)
  s1.append (s2.append (s3.append (s4.append s5)))


end Lattice
end StatMech
