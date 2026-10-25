/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripMasses


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

def hexCSClassIncidences
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass) :
    Finset (HexCSIncidence T L) :=
  (hexCSBoundaryIncidences T L \ {hexCSStartIncidence T L hT}).filter
    (fun e => hexCSBoundaryClass e = cls)

end
end StatMech.Universality
