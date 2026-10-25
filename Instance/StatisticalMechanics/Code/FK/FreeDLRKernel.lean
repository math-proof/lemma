/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.CrossBoxGeneralKeystone.Part3
import Theorem.StatisticalMechanics.Code.FK.DlrInfiniteSandwich
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
open MeasureTheory Set SimpleGraph Filter Topology
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {Vin Vout : Type*} [Fintype Vin] [DecidableEq Vin]
  [Fintype Vout] [DecidableEq Vout]


instance (priority := 10000) : MeasurableSpace (SimpleGraph Vin) := ⊤

instance : DiscreteMeasurableSpace (SimpleGraph Vin) := ⟨fun _ => trivial⟩

instance : TopologicalSpace (SimpleGraph Vin) := ⊥

instance : DiscreteTopology (SimpleGraph Vin) := ⟨rfl⟩


end FK
end StatMech
