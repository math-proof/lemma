/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanCoresUnify.Part2
import Theorem.StatisticalMechanics.Code.Walls.dg2degree.Part5
import Theorem.StatisticalMechanics.Code.Walls.npjnopinch
open SimpleGraph Set


namespace StatMech

namespace Walls

open StatMech.Lattice

attribute [local instance] Classical.propDecidable


def npj_SeparatingSideResidue (a b : ℤ)
    (wK : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b)) : Prop :=
  jcu_HasSeparatingSide Set.univ {z | z ∈ wK.support} {npj_c10 a b} {npj_c01 a b}


end Walls
end StatMech
