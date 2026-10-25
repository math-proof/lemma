/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part3
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]


namespace EdgeCount

noncomputable def edgeAxisI (d n : ℕ) (i : Fin d) : Finset (Site d × Site d) :=
  (boxSV_edgeF d n).filter (fun p => p.1 i ≠ p.2 i)

noncomputable def shiftDom (d n : ℕ) (i : Fin d) (b : ℤ) : Finset (Site d) :=
  (boxSV_boxF d n).filter (fun x => x i + b ∈ Finset.Icc (-(n : ℤ)) n)

noncomputable def shiftMap (d n : ℕ) (i : Fin d) (b : ℤ) (x : Site d) : Site d × Site d :=
  (x, Function.update x i (x i + b))

end EdgeCount
end FK
end StatMech
