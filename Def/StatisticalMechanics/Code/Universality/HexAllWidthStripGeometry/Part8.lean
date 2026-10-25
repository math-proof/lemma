/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part6


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexAWMids (T L : ℕ) : Finset ℂ :=
  (Finset.univ : Finset (HexAWVertex T L)).biUnion
    (fun v => (Finset.univ : Finset (Fin 3)).image
      (fun e => hexAWMid v.1 e))

end
end StatMech.Universality
