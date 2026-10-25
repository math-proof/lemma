/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseConstant.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheCyclicWord {m : Nat} (a t : Fin (m + 1)) :
    Finset (Fin (m + 1)) :=
  Finset.univ.filter fun k =>
    0 < (k - a).val ∧ (k - a).val ≤ (t - a).val

end
end StatMech.FrontierD
