/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MultibondReindex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetGauge
open Finset


namespace StatMech.FrontierA

noncomputable section

variable {P P' V V' : Type*}
  [Fintype P] [DecidableEq P] [Fintype P'] [DecidableEq P']
  [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']


def multibondConfigReindex (eV : V ≃ V') : (V -> Bool) ≃ (V' -> Bool) where
  toFun s v := s (eV.symm v)
  invFun s v := s (eV v)
  left_inv s := by funext v; simp
  right_inv s := by funext v; simp

end
end StatMech.FrontierA
