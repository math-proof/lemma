/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part3
open Finset SimpleGraph Set


namespace StatMech

namespace BeffaraDC

open Lattice Ising Walls


def pfdOpenPlanar (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (hKP : K ≤ P.G) :
    PlanarZ2Subgraph where
  V := P.V
  finV := P.finV
  decV := P.decV
  G := K
  emb := P.emb
  isSub := by
    intro x y h
    exact P.isSub (hKP h)

end BeffaraDC
end StatMech
