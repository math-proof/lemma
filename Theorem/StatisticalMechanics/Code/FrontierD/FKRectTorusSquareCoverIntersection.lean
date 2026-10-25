/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

@[simp] theorem fkRectIntegralSquareDartMod_site
    (L : Nat) (d : FKRectIntegralSquareDart) :
    (fkRectIntegralSquareDartMod L d).1 =
      ((d.1.1 : ZMod L), (d.1.2 : ZMod L)) :=
  rfl

theorem fkRectIntegralSquareDartMod_end
    (L : Nat) (d : FKRectIntegralSquareDart) :
    ons_dirStep L (fkRectIntegralSquareDartMod L d).2
        (fkRectIntegralSquareDartMod L d).1 =
      (((fkRectIntegralSquareDartEnd d).1 : ZMod L),
        ((fkRectIntegralSquareDartEnd d).2 : ZMod L)) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;>
    simp [fkRectIntegralSquareDartMod, fkRectIntegralSquareDartEnd,
      ons_dirStep, ons_dirExponentX, ons_dirExponentY] <;> ring


theorem FKRectSquareAxisStep.exists_direction
    {p q : Int × Int} (h : FKRectSquareAxisStep p q) :
    ∃ mu : Fin 4, fkRectIntegralSquareDartEnd (p, mu) = q := by
  rcases h with h | h | h | h
  · refine ⟨2, ?_⟩
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp [fkRectIntegralSquareDartEnd, ons_dirExponentX,
        ons_dirExponentY] at * <;> omega
  · refine ⟨1, ?_⟩
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp [fkRectIntegralSquareDartEnd, ons_dirExponentX,
        ons_dirExponentY] at * <;> omega
  · refine ⟨0, ?_⟩
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp [fkRectIntegralSquareDartEnd, ons_dirExponentX,
        ons_dirExponentY] at * <;> omega
  · refine ⟨3, ?_⟩
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp [fkRectIntegralSquareDartEnd, ons_dirExponentX,
        ons_dirExponentY] at * <;> omega


end
end StatMech.FrontierD
