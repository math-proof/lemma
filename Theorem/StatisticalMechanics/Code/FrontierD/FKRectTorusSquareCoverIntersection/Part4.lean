/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part3
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

theorem FKRectIntegralSquareDartPath.repeatTranslated
    {p u : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p
      (p.1 + u.1, p.2 + u.2) l) (n : Nat) :
    FKRectIntegralSquareDartPath p
      (p.1 + (n : Int) * u.1, p.2 + (n : Int) * u.2)
      (fkRectRepeatTranslatedDartPath l u n) := by
  induction n with
  | zero =>
      simpa [fkRectRepeatTranslatedDartPath] using
        (FKRectIntegralSquareDartPath.nil p)
  | succ n ih =>
      have htranslate := h.translate (fkRectNatScale n u)
      have happend := ih.append htranslate
      have hend :
          ((p.1 + u.1, p.2 + u.2).1 + (fkRectNatScale n u).1,
              (p.1 + u.1, p.2 + u.2).2 + (fkRectNatScale n u).2) =
            (p.1 + ((n + 1 : Nat) : Int) * u.1,
              p.2 + ((n + 1 : Nat) : Int) * u.2) := by
        apply Prod.ext <;>
          simp [fkRectNatScale, Nat.cast_add, Nat.cast_one] <;> ring
      rw [hend] at happend
      rw [fkRectRepeatTranslatedDartPath]
      exact happend


end
end StatMech.FrontierD
