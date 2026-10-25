/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InsideCoveringClose
import Theorem.StatisticalMechanics.Code.Ising.PeierlsPlanarAssembly
import Theorem.StatisticalMechanics.Code.Ising.PeierlsArcAssembly.Part2
open Set SimpleGraph Function


set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice


variable {W : Type*} {G : SimpleGraph W}


variable {V : Type*} [Finite V] [DecidableEq V]


def paa_ArcNoSeparationOff (Vc : (hypercubicLattice 2).Walk a a)
    (a' b' : {z : Site 2 // z ∉ Vc.support}) : Prop :=
  s(a', b') ∉ (icc_offComplGraph Vc).edgeSet ∧
    (icc_offComplGraph Vc ⊔ edge a' b').Connected


end Ising
end StatMech
