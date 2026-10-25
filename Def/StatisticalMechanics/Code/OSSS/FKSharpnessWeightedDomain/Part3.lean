/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomain.Part2
open scoped BigOperators Classical
open Finset Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


noncomputable def condBcProbW (pf : Sym2 V -> Real) (q : Real)
    (F : Finset (Sym2 V)) (psi omega : ConfigSpace (Sym2 V)) : Real :=
  if AgreesOff F psi omega then
    bcWeightW G C pf q omega / inducedBcZW G C pf q F psi
  else 0

end FK
end StatMech
