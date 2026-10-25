/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalPlusCorrDecay
import Abbrev.StatisticalMechanics.Code.FrontierA.Z2GaugeInternalCylinderCoordinates


namespace StatMech.FrontierA

open StatMech StatMech.Lattice

noncomputable section

def internalCylinderBoundaryIndices (N : Nat) :
    Finset (CubicalCell N N N) :=
  (Finset.univ : Finset (CubicalCell N N N)).filter fun q =>
    q.x.val = 0 ∨ q.x.val + 1 = N ∨
    q.y.val = 0 ∨ q.y.val + 1 = N ∨
    q.z.val + 1 = N


def internalCylinderUpperCell (N m : Nat) (hNm : N <= m)
    (ij : internalCylinderUpperIndex N) :
    CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) :=
  CubicalCell.mk
    ⟨m + ij.1.val, by dsimp [oddCubeSide]; omega⟩
    ⟨m + ij.2.val, by dsimp [oddCubeSide]; omega⟩
    ⟨m, by dsimp [oddCubeSide]; omega⟩


def internalCylinderBoundaryCell (N m : Nat) (hN : 0 < N) (hNm : N <= m)
    (q : CubicalCell N N N) :
    CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) :=
  CubicalCell.mk
    ⟨m + q.x.val, by dsimp [oddCubeSide]; omega⟩
    ⟨m + q.y.val, by dsimp [oddCubeSide]; omega⟩
    ⟨m - 1 - q.z.val, by dsimp [oddCubeSide]; omega⟩


def internalCylinderBoundaryCoordinateVertices
    (N m : Nat) (hN : 0 < N) (hNm : N ≤ m) :
    Finset (CubicalDualVertex (oddCubeSide m) (oddCubeSide m)
      (oddCubeSide m)) :=
  (internalCylinderBoundaryIndices N).image fun q =>
    some (internalCylinderBoundaryCell N m hN hNm q)


def internalCylinderUpperSite {N : Nat}
    (ij : internalCylinderUpperIndex N) : Site 3 := fun k =>
  if k = (0 : Fin 3) then ij.1.val
  else if k = (1 : Fin 3) then ij.2.val
  else 0


def internalCylinderBoundarySite {N : Nat}
    (q : CubicalCell N N N) : Site 3 := fun k =>
  if k = (0 : Fin 3) then q.x.val
  else if k = (1 : Fin 3) then q.y.val
  else q.z.val + 1

end
end StatMech.FrontierA
