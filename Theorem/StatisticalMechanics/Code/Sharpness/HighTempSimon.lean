/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Def.StatisticalMechanics.Code.Sharpness.HighTempSimon
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem mem_highTempInternalEdges (S : Finset V) (e : Sym2 V) :
    e ∈ highTempInternalEdges G S ↔
      e ∈ G.edgeFinset ∧ edgeInside S e := by
  simp [highTempInternalEdges]


end Sharpness
end StatMech
