/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
open scoped BigOperators Classical
open Finset Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


noncomputable def bcWeightW (pf : Sym2 V -> Real) (q : Real)
    (omega : ConfigSpace (Sym2 V)) : Real :=
  edgeProductW G pf omega * q ^ numClustersBC G C omega


noncomputable def bcZW (pf : Sym2 V -> Real) (q : Real) : Real :=
  ∑ omega, bcWeightW G C pf q omega


noncomputable def bcProbW (pf : Sym2 V -> Real) (q : Real)
    (omega : ConfigSpace (Sym2 V)) : Real :=
  bcWeightW G C pf q omega / bcZW G C pf q

end FK
end StatMech
