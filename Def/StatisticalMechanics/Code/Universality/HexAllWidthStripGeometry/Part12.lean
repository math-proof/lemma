/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part10


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexAWIncidences (T L : ℕ) : Finset (HexAWIncidence T L) :=
  ((Finset.univ : Finset (HexAWVertex T L)) ×ˢ
      (Finset.univ : Finset (Fin 3))).image
    (fun p => ⟨p.1, p.2⟩)

end
end StatMech.Universality
