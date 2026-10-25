/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

@[simp] theorem hexAWDomain_interiorVertices (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) :
    (hexAWDomain T L hT hlocal).interiorVertices = Finset.univ := rfl

@[simp] theorem hexAWDomain_pos (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) (v : HexAWVertex T L) :
    (hexAWDomain T L hT hlocal).pos v = hexAWPos v.1 := rfl

@[simp] theorem hexAWDomain_mid (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) (v : HexAWVertex T L)
    (j : Fin 3) :
    (hexAWDomain T L hT hlocal).mid v j = hexAWMid v.1 j := rfl

@[simp] theorem hexAWDomain_obs (T L : ℕ) (hT : 0 < T)
    (hlocal : HexAWLocalRelation T L hT) (z : ℂ) :
    (hexAWDomain T L hT hlocal).obs z = hexAWObservable T L hT z := rfl


end
end StatMech.Universality
