/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TiltSecant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose3
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FK.TiltSecant
open MeasureTheory Set Filter Topology Real
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


def FKSecantData (d N : ℕ) (eb : Sym2 (boxVerts d N)) : Prop :=
  ∃ S V : ℕ → ℝ, (∀ n, 0 < V n)
    ∧ Tendsto (fun n => S n / V n) atTop (𝓝 0)
    ∧ Tendsto V atTop atTop
    ∧ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p → ∀ ε > 0, ∀ n,
        ε ≤ (2 : ℝ) ^ (S n)
          * (tiltFactor p p')
              ^ ((wiredEdgeDensity d 2 (edgeIncl d N eb) p'
                    - freeEdgeDensity d 2 (edgeIncl d N eb) p - 2 * ε) * V n) / ε


end FK
end StatMech
