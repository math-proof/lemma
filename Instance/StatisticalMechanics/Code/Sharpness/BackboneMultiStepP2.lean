/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepP2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneMultiStepBondProgram.Part4
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneMultiStepBondProgram

open BackboneConcreteSelector

open BackboneConcreteBondProgram

noncomputable local instance multiStepP2DecidableAdj
    (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _


end BackboneMultiStepBondProgram
end
end StatMech.Sharpness
