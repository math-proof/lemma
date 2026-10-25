/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part6
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPrimalDualCrossingRepresentativeSourceIndex_injective
    (R : FKRectTorus) (eta : R.Configuration) :
    Function.Injective
      (fkRectPrimalDualCrossingRepresentativeSourceIndex R eta) := by
  intro C D hCD
  rcases C with C | C <;> rcases D with D | D
  · simp only [fkRectPrimalDualCrossingRepresentativeSourceIndex,
      Equiv.apply_eq_iff_eq, Sum.inl.injEq] at hCD
    exact congrArg Sum.inl
      (fkRectRawHorizontalCrossingRepresentative_injective R _ hCD)
  · simp [fkRectPrimalDualCrossingRepresentativeSourceIndex] at hCD
  · simp [fkRectPrimalDualCrossingRepresentativeSourceIndex] at hCD
  · simp only [fkRectPrimalDualCrossingRepresentativeSourceIndex,
      Equiv.apply_eq_iff_eq, Sum.inr.injEq] at hCD
    exact congrArg Sum.inr
      (fkRectRawHorizontalCrossingRepresentative_injective R _ hCD)

end
end StatMech.FrontierD
