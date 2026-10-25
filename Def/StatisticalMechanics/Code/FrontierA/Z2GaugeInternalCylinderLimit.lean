/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalPlusCorrDecay
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

def internalCentralCellEmbedding (n m : Nat)
    (hnm : centralSquareSide n < m) :
    CubicalCell (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n) ↪
      CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) where
  toFun q := CubicalCell.mk
    ⟨m + q.x.val, by
      dsimp [oddCubeSide, centralSquareSide] at *
      omega⟩
    ⟨m + q.y.val, by
      dsimp [oddCubeSide, centralSquareSide] at *
      omega⟩
    ⟨m - centralSquareSide n + q.z.val, by
      dsimp [oddCubeSide, centralSquareSide] at *
      omega⟩
  inj' := by
    intro q r h
    rcases q with ⟨qx, qy, qz⟩
    rcases r with ⟨rx, ry, rz⟩
    simp only [CubicalCell.mk.injEq] at h
    simp only [CubicalCell.mk.injEq]
    constructor
    · apply Fin.ext
      have := congrArg Fin.val h.1
      simp only at this
      omega
    constructor
    · apply Fin.ext
      have := congrArg Fin.val h.2.1
      simp only at this
      omega
    · apply Fin.ext
      have := congrArg Fin.val h.2.2
      simp only at this
      omega


def internalCentralVertexEmbedding (n m : Nat)
    (hnm : centralSquareSide n < m) :
    CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n) ↪
      CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) :=
  (internalCentralCellEmbedding n m hnm).optionMap

end
end StatMech.FrontierA
