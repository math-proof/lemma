/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Instance.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

def hexCSMids (T L : ℕ) : Finset ℂ :=
  (Finset.univ : Finset (HexCSVertex T L)).biUnion
    (fun v => (Finset.univ : Finset (Fin 3)).image
      (fun e => hexAWMid v.1 e))

end
end StatMech.Universality
