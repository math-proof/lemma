/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Instance.StatisticalMechanics.Code.Sharpness.HighTempSimon
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def HighTempSwitchOutput.Valid (S : Finset V) (o z : V)
    (r : HighTempSwitchOutput (V := V)) : Prop :=
  r.x ∈ S ∧ r.y ∉ S ∧
    r.A ⊆ highTempInternalEdges G S ∧
    r.B ⊆ G.edgeFinset ∧
    HasOddBoundary r.A (sourcePair o r.x) ∧
    HasOddBoundary r.B (sourcePair r.y z)

end Sharpness
end StatMech
