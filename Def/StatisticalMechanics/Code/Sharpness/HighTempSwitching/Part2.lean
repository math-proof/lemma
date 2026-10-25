/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSources.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part3
open Finset
open scoped symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def highTempFirstExit (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Finset (Sym2 V)) (hK : K ⊆ G.edgeFinset) {o z : V}
    (hbd : HasOddBoundary K (sourcePair o z)) (S : Finset V)
    (ho : o ∈ S) (hz : z ∉ S) : HighTempFirstExit K o z S :=
  (exists_highTempFirstExit G K hK hbd S ho hz).some


end Sharpness
end StatMech
