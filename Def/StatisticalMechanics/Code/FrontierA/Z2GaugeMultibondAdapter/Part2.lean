/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeMultibondAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeMultibondAdapter
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

variable {E P V : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]


def multibondIsingWeight (ends : P → V × V) (J : P → Real)
    (s : V → Bool) : Real :=
  Real.exp (∑ p : P,
    J p * if s (ends p).1 = s (ends p).2 then 1 else -1)


def multibondIsingPartition (ends : P → V × V) (J : P → Real) : Real :=
  ∑ s : V → Bool, multibondIsingWeight ends J s


end
end StatMech.FrontierA
