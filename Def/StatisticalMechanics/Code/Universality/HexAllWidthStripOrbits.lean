/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable def hexAWObservable (T L : ℕ) (hT : 0 < T) (z : ℂ) : ℂ :=
  parafObservable (hexAWFiniteRegion T L hT).inRegion
    (hexAWFiniteRegion T L hT).start 1 z (5 / 8) hexChi


def HexAWLocalRelation (T L : ℕ) (hT : 0 < T) : Prop :=
  ∀ v : HexAWVertex T L,
    ∑ j : Fin 3,
      (hexAWMid v.1 j - hexAWPos v.1) *
        hexAWObservable T L hT (hexAWMid v.1 j) = 0


noncomputable def hexAWDomain (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) :
    HexDomain (HexAWVertex T L) where
  interiorVertices := Finset.univ
  pos v := hexAWPos v.1
  mid v j := hexAWMid v.1 j
  obs := hexAWObservable T L hT
  relation := by
    intro v _
    exact hlocal v

end
end StatMech.Universality
