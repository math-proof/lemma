/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MultiEdgeDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Theorem.StatisticalMechanics.Code.FK.OffCentreCarrier
import Theorem.StatisticalMechanics.Code.FK.MultiEdgeDecay
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def med_multiMassProb (μ : ConfigSpace (Sym2 V) → ℝ) (t : Finset (Sym2 V)) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V),
    (med_genericMultiOpenEvent t).indicator (fun _ => (1:ℝ)) ω * μ ω


end FK
end StatMech
