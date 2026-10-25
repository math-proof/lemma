/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexEvenSymmetricBetheResidual
    (N m : Nat) (c : Real) (q : Fin m → Real) : Fin m → Real :=
  fun j => sixVertexBetheResidual c N (m + m)
    (sixVertexEvenSymmetricLift m q) (Fin.natAdd m j)


def sixVertexEvenSymmetricBetheResidualGraph (N m : Nat) :
    (Real × (Fin m → Real)) → (Real × (Fin m → Real)) :=
  fun q => (q.1, sixVertexEvenSymmetricBetheResidual N m q.1 q.2)

end
end StatMech.FrontierD
