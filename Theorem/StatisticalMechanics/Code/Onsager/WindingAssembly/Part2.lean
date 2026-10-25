/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.GroundUpWinding.Part4
import Theorem.StatisticalMechanics.Code.Onsager.SplitConstruction
import Theorem.StatisticalMechanics.Code.Onsager.PolygonWalk.Part3
import Def.StatisticalMechanics.Code.Onsager.WindingAssembly.Part2


namespace StatMech.Onsager.WindingAssembly

open StatMech.Onsager.SplitConstruction


theorem propIV_conditional
    (hbase : ∀ V : List Pt, simplePred V → rcCount V = 0 → ccCount V = 4)
    (hchord : ∀ V : List Pt, simplePred V → 0 < rcCount V →
        ∃ a b : ℕ, a + 1 < b ∧ b < V.length ∧ (0 < a ∨ b + 1 < V.length) ∧
          isAxisAligned V[a]! V[b]! ∧
          ccCount (arc V a b) + ccCount (coarc V a b) = ccCount V + 3 ∧
          rcCount (arc V a b) + rcCount (coarc V a b) = rcCount V - 1)
    (V : List Pt) (hV : simplePred V) :
    ccCount V - rcCount V = 4 :=
  (concretePolyData hbase hchord).umlaufsatz V hV

end StatMech.Onsager.WindingAssembly
