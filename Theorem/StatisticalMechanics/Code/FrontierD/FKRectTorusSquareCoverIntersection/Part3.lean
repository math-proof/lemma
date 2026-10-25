/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part2
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

theorem fkRectIntegralSquareDartEnd_translate
    (u : Int × Int) (d : FKRectIntegralSquareDart) :
    fkRectIntegralSquareDartEnd
        (fkRectIntegralSquareDartTranslate u d) =
      ((fkRectIntegralSquareDartEnd d).1 + u.1,
        (fkRectIntegralSquareDartEnd d).2 + u.2) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  apply Prod.ext <;>
    simp [fkRectIntegralSquareDartTranslate,
      fkRectIntegralSquareDartEnd] <;> ring


theorem FKRectIntegralSquareDartPath.translate
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) (u : Int × Int) :
    FKRectIntegralSquareDartPath
      (p.1 + u.1, p.2 + u.2) (q.1 + u.1, q.2 + u.2)
      (l.map (fkRectIntegralSquareDartTranslate u)) := by
  induction h with
  | nil p =>
      exact FKRectIntegralSquareDartPath.nil _
  | @cons d q r l hend tail ih =>
      apply FKRectIntegralSquareDartPath.cons
        (fkRectIntegralSquareDartTranslate u d)
      · rw [fkRectIntegralSquareDartEnd_translate, hend]
      · exact ih


theorem FKRectIntegralSquareDartPath.append
    {p q r : Int × Int} {l k : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l)
    (g : FKRectIntegralSquareDartPath q r k) :
    FKRectIntegralSquareDartPath p r (l ++ k) := by
  induction h with
  | nil p => simpa using g
  | cons d hend tail ih =>
      exact FKRectIntegralSquareDartPath.cons d hend (ih g)


end
end StatMech.FrontierD
