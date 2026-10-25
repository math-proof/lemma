/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhasePerturbation.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexBethePerturbedWordTerm
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (eps : Real) (x : Fin (n + 1) → Int)
    (w : Finset (Fin (n + 1))) (sigma : Equiv.Perm (Fin (n + 1))) :
    Complex :=
  sixVertexBetheAmplitude c p sigma *
    sixVertexBetheWordCoefficient c
      (fun j => sixVertexBethePhase
        (sixVertexBethePerturbRoot p ell eps j)) sigma w *
    sixVertexBetheWordMonomial N
      (fun j => sixVertexBethePhase
        (sixVertexBethePerturbRoot p ell eps j)) sigma x w

end
end StatMech.FrontierD
