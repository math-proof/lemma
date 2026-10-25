/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part4
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectPrimalDualCrossingSourceIndexEquiv (R : FKRectTorus) :
    Fin R.height ⊕ Fin R.height ≃ Fin (2 * R.height) :=
  finSumFinEquiv.trans (finCongr (two_mul R.height).symm)

def FKRectPrimalDualCrossingSourceSum
    (R : FKRectTorus) (eta : R.Configuration) :
    Fin R.height ⊕ Fin R.height -> Prop
  | Sum.inl y => FKRectRawHorizontalCrossingSource R
      (fkRectForceCutClosed R eta) y
  | Sum.inr y => FKRectRawHorizontalCrossingSource R
      (fkRectDualConfigurationEquiv R
        (fkRectForceCutClosed R eta)) y


def FKRectPrimalDualCrossingSource
    (R : FKRectTorus) (eta : R.Configuration)
    (i : Fin (2 * R.height)) : Prop :=
  FKRectPrimalDualCrossingSourceSum R eta
    ((fkRectPrimalDualCrossingSourceIndexEquiv R).symm i)

noncomputable def fkRectPrimalDualCrossingSourceSubtypeEquiv
    (R : FKRectTorus) (eta : R.Configuration) :
    {i : Fin (2 * R.height) // FKRectPrimalDualCrossingSource R eta i} ≃
      {y : Fin R.height // FKRectRawHorizontalCrossingSource R
        (fkRectForceCutClosed R eta) y} ⊕
      {y : Fin R.height // FKRectRawHorizontalCrossingSource R
        (fkRectDualConfigurationEquiv R
          (fkRectForceCutClosed R eta)) y} := by
  let e := fkRectPrimalDualCrossingSourceIndexEquiv R
  let h :
      {s : Fin R.height ⊕ Fin R.height //
        FKRectPrimalDualCrossingSourceSum R eta s} ≃
        {i : Fin (2 * R.height) //
          FKRectPrimalDualCrossingSource R eta i} :=
    Equiv.subtypeEquiv e (fun s => by
      change FKRectPrimalDualCrossingSourceSum R eta s ↔
        FKRectPrimalDualCrossingSourceSum R eta (e.symm (e s))
      rw [e.symm_apply_apply])
  exact h.symm.trans Equiv.subtypeSum

end
end StatMech.FrontierD
