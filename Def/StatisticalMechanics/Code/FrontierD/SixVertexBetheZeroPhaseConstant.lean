/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseCancellation.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseConstant
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexBethePerturbedConstantWordTotal
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (x : Fin (n + 1) → Int) (eps : Real) : Complex :=
  ∑ sigma : Equiv.Perm (Fin (n + 1)), (
    sixVertexBethePerturbedWordTerm N c p ell eps x ∅ sigma +
      sixVertexBethePerturbedWordTerm N c p ell eps x Finset.univ sigma)

end
end StatMech.FrontierD
