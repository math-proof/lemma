/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part3
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace


variable {E F : Type*}


def cfgEquiv (e : E ≃ F) : ConfigSpace F ≃ ConfigSpace E where
  toFun ω := fun x => ω (e x)
  invFun ω := fun y => ω (e.symm y)
  left_inv ω := by funext y; simp
  right_inv ω := by funext x; simp

end StatMech
