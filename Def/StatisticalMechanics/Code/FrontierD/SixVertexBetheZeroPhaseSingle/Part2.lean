/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseConstant.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheZeroHatCoefficient
    {n : Nat} (c : Real) (p : Fin (n + 1) → Real)
    (sigma : Equiv.Perm (Fin (n + 1)))
    (w : Finset (Fin (n + 1))) (a : Fin (n + 1)) : Complex :=
  sixVertexBetheM c (sixVertexBethePhase (p (sigma a))) *
    sixVertexBetheWordCoefficientRemainder c
      (fun j => sixVertexBethePhase (p j)) sigma w a

def sixVertexBetheZeroHatTerm
    {n N : Nat} (c : Real) (p : Fin (n + 1) → Real)
    (sigma : Equiv.Perm (Fin (n + 1)))
    (x : Fin (n + 1) → Int) (w : Finset (Fin (n + 1)))
    (a : Fin (n + 1)) : Complex :=
  sixVertexBetheAmplitude c p sigma *
    sixVertexBetheZeroHatCoefficient c p sigma w a *
      sixVertexBetheWordMonomial N
        (fun j => sixVertexBethePhase (p j)) sigma x w

end
end StatMech.FrontierD
