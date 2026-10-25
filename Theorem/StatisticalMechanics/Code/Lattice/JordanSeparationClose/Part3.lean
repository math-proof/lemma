/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanSeparationClose.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem jsc_unitSquareLoop_inside_odd :
    ¬ Even (jec_rayCount (![1, 1] : Site 2) jsc_unitSquareLoop) := by
  have hcount : jec_rayCount (![1, 1] : Site 2) jsc_unitSquareLoop = 1 := by
    unfold jsc_unitSquareLoop
    simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
      jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    norm_num
  rw [hcount]; decide


theorem jsc_JordanSeparates_inside_satisfiable :
    ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a), ∃ p, ¬ Even (jec_rayCount p Vc) :=
  ⟨_, jsc_unitSquareLoop, _, jsc_unitSquareLoop_inside_odd⟩

end Lattice
end StatMech
