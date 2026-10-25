/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Structure.StatisticalMechanics.Code.Sharpness.HighTempSimon
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def HighTempSwitchInput.Valid (S : Finset V) (o z : V)
    (p : HighTempSwitchInput (V := V)) : Prop :=
  p.F ⊆ G.edgeFinset ∧
    p.H ⊆ highTempInternalEdges G S ∧
    HasOddBoundary p.F (sourcePair o z) ∧
    HasOddBoundary p.H ∅

end Sharpness
end StatMech
