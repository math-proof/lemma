/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardExtremeVertex
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardSupportingChord


namespace StatMech.FrontierA

def KWFiniteSimplePolygon.ChordIsClean {n : ℕ} [NeZero n]
    (polygon : KWFiniteSimplePolygon n) (i j : Fin n) : Prop :=
  (∀ k : Fin n, k ≠ i → k ≠ j →
      ¬Sbtw ℝ (polygon.vertex i) (polygon.vertex k) (polygon.vertex j)) ∧
    ∀ k : Fin n,
      Disjoint
        {z : ℂ | Sbtw ℝ (polygon.vertex i) z (polygon.vertex j)}
        {z : ℂ | Sbtw ℝ (polygon.vertex k) z
          (polygon.vertex (k + 1))}

end StatMech.FrontierA
