/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part6
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

instance : Unique (Equiv.Perm (Fin 1)) where
  default := 1
  uniq σ := by
    ext i
    fin_cases i
    simp


end
end StatMech.FrontierD
