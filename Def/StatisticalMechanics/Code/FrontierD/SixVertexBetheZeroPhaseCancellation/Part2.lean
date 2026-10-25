/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhasePerturbation.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseCancellation
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheMLBoundarySet {n : Nat}
    (w : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i => i ∉ w ∧ finRotate (n + 1) i ∈ w

end
end StatMech.FrontierD
