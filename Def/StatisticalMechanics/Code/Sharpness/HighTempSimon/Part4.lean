/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Instance.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part2
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def highTempSwitchInputs (S : Finset V) (o z : V) :
    Finset (HighTempSwitchInput (V := V)) :=
  Finset.univ.filter (HighTempSwitchInput.Valid G S o z)

noncomputable def highTempSwitchOutputs (S : Finset V) (o z : V) :
    Finset (HighTempSwitchOutput (V := V)) :=
  Finset.univ.filter (HighTempSwitchOutput.Valid G S o z)


end Sharpness
end StatMech
