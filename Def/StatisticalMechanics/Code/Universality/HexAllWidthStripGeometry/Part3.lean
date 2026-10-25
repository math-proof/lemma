/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Instance.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexAWCoordBox (T L : ℕ) : Finset HexAWCoord :=
  (((Finset.Icc (-(2 * (T + L) + 2 : ℕ) : ℤ)
        (2 * (T + L) + 2 : ℕ)).product
      (Finset.Icc (-(2 * (T + L) + 2 : ℕ) : ℤ)
        (2 * (T + L) + 2 : ℕ))).product
      (Finset.univ : Finset HexAWColor)).image
    (fun p => ⟨p.1.1, p.1.2, p.2⟩)


def hexAWVertexSet (T L : ℕ) : Finset HexAWCoord :=
  (hexAWCoordBox T L).filter (hexAWInStrip T L)


end
end StatMech.Universality
