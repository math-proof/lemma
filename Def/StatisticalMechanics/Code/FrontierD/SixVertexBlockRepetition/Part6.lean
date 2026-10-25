/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part6
open Finset


namespace StatMech.FrontierD

def sixVertexStraightExtendedToroidalBoundary {N M r : ℕ}
    (q : ℕ) (ξ : SixVertexToroidalBoundary N M) (z : Fin r → Bool) :
    SixVertexToroidalBoundary (N + r) (M + q) :=
  (Fin.addCases ξ.1 (fun _ : Fin q => false), Fin.addCases ξ.2 z)


end StatMech.FrontierD
