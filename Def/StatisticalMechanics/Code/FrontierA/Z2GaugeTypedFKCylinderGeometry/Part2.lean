/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

def squareLayerExpSum {N : Nat} (r : Real) (x y : Fin N)
    (depth : Nat) : Real :=
  ∑ ij : Fin N × Fin N,
    r ^ (Nat.dist x.val ij.1.val + Nat.dist y.val ij.2.val + depth)


def squareLowerCapExpSum (r : Real) (N : Nat) : Real :=
  ∑ xy : Fin N × Fin N, squareLayerExpSum r xy.1 xy.2 N


def squareXSideExpSum {N : Nat} (r : Real) (xBoundary : Fin N) : Real :=
  ∑ yz : Fin N × Fin N,
    squareLayerExpSum r xBoundary yz.1 (N - yz.2.val)


def squareYSideExpSum {N : Nat} (r : Real) (yBoundary : Fin N) : Real :=
  ∑ xz : Fin N × Fin N,
    squareLayerExpSum r xz.1 yBoundary (N - xz.2.val)

end
end StatMech.FrontierA
