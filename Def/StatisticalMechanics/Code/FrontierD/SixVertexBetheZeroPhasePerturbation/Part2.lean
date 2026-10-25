/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhasePerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddPhysicalExpansion
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhasePerturbation
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexBethePerturbedIntervalTotal
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (x : Fin (n + 1) → Int) (eps : Real) : Complex :=
  ∑ sigma : Equiv.Perm (Fin (n + 1)),
    sixVertexBetheAmplitude c p sigma *
      sixVertexBetheCollisionFreeIntervalSum N c
        (fun i => sixVertexBethePhase
          (sixVertexBethePerturbRoot p ell eps (sigma i))) x


def sixVertexBethePerturbedWordTotal
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (x : Fin (n + 1) → Int) (eps : Real) : Complex :=
  ∑ sigma : Equiv.Perm (Fin (n + 1)),
    sixVertexBetheAmplitude c p sigma *
      ∑ w : Finset (Fin (n + 1)),
        sixVertexBetheWordCoefficient c
            (fun j => sixVertexBethePhase
              (sixVertexBethePerturbRoot p ell eps j)) sigma w *
          sixVertexBetheWordMonomial N
            (fun j => sixVertexBethePhase
              (sixVertexBethePerturbRoot p ell eps j)) sigma x w

end
end StatMech.FrontierD
