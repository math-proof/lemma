/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingClose.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepDual.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

noncomputable def jkd_ringP : PlanarZ2Subgraph where
  V := Fin 9
  finV := inferInstance
  decV := inferInstance
  G := jkd_gr9G
  emb := ⟨jkd_gr9emb, jkd_gr9emb_inj⟩
  isSub := jkd_gr9_isSub


def jkd_r0 : Fin 9 := 0

def jkd_r1 : Fin 9 := 1

end Lattice
end StatMech
