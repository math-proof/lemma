/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKPressureDeriv.Part4
import Theorem.StatisticalMechanics.Code.FK.AvgDensityCollapse
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
import Theorem.StatisticalMechanics.Code.FK.FKDensityDeriv
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {d : ℕ}


def fdd_FreeDensityIsLeftDeriv (N : ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureLeftDeriv g t


def fdd_WiredDensityIsRightDeriv (N : ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureRightDeriv g t


def fdd_WiredDensityUpperBound (N : ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ≤ pressureRightDeriv g t


end FK
end StatMech
