/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part6
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexSingletonSector {N : ℕ} (i : Fin N) : SixVertexSector N 1 :=
  ⟨{i}, by simp⟩

end
end StatMech.FrontierD
