/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part88
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


def rlc_dualReflectFun (x : Site 2) : Site 2 := ![-x 0 - 1, x 1 + 1]


def rlc_dualReflectInvFun (x : Site 2) : Site 2 := ![-x 0 - 1, x 1 - 1]


def rlc_dualReflect : Site 2 ≃ Site 2 where
  toFun := rlc_dualReflectFun
  invFun := rlc_dualReflectInvFun
  left_inv x := by
    ext i
    fin_cases i <;> simp [rlc_dualReflectFun, rlc_dualReflectInvFun]
  right_inv x := by
    ext i
    fin_cases i <;> simp [rlc_dualReflectFun, rlc_dualReflectInvFun]

end Universality
end StatMech
