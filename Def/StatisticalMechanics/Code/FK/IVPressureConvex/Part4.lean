/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
import Theorem.StatisticalMechanics.Code.FK.IVPressureConvex.Part4
open MeasureTheory Set Filter Topology Real Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {ι : Type*} [Fintype ι]


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def ivp2_softplus (t : ℝ) : ℝ := Real.log (1 + Real.exp t)


end FK
end StatMech
