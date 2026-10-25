/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectVerticalCrossingEvent_isIncreasing
    (R : FKRectTorus) (x0 x1 y0 y1 : Nat) :
    IsIncreasing (fkRectVerticalCrossingEvent R x0 x1 y0 y1) := by
  intro omega tau hopen
  rintro ⟨x, y, hx, hy, hxy⟩
  exact ⟨x, y, hx, hy, hxy.mono_configuration R hopen _⟩

theorem fkRectHorizontalCrossingEvent_isIncreasing
    (R : FKRectTorus) (x0 x1 y0 y1 : Nat) :
    IsIncreasing (fkRectHorizontalCrossingEvent R x0 x1 y0 y1) := by
  intro omega tau hopen
  rintro ⟨x, y, hx, hy, hxy⟩
  exact ⟨x, y, hx, hy, hxy.mono_configuration R hopen _⟩


end
end StatMech.FrontierD
