/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessDensity
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose2
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part5
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.Foundations.Strassen
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part2
open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {E : Type*} [Fintype E] [DecidableEq E]


variable {d : ℕ}


def fuc_HomogeneousFreeEnergyData (d N : ℕ) : Prop :=
  ∃ g : ℝ → ℝ, ConvexOn ℝ univ g
    ∧ (∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
        wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureRightDeriv g t)
    ∧ (∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
        freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureLeftDeriv g t)


end FK
end StatMech
