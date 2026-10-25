/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FeketeLimit
import Theorem.StatisticalMechanics.Code.FK.ConvexDerivLimit
import Theorem.StatisticalMechanics.Code.FK.IVPressureConvex.Part5
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBeta.Part4
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.FKPressureDeriv
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {d : ℕ}


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def fpd_avgDensity (t : ℝ) : ℝ :=
  (1 / (G.edgeFinset.card : ℝ)) * fkExpect G (fsc_logistic t) 2 (fun ω => (openCount G ω : ℝ))


end FK
end StatMech
