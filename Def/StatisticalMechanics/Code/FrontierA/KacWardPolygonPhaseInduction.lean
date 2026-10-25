/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPhaseInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordEndpointOrder.Part3


namespace StatMech.FrontierA

def KWCleanChordPhaseCompatibility : Prop :=
  ∀ {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (_hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (j : Fin n) (hj : 2 ≤ j.val) (_hjupper : j.val + 2 ≤ n)
    (_hclean : polygon.ChordIsClean 0 j),
    polygon.CleanChordEndpointOrder j (by omega)


end StatMech.FrontierA
