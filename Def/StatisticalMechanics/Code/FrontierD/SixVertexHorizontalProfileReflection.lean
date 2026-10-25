/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexCyclicNeg {N : Nat} (hN : 0 < N) (i : Fin N) : Fin N :=
  if hi : i.val = 0 then ⟨0, hN⟩ else
    ⟨N - i.val, Nat.sub_lt hN (Nat.pos_of_ne_zero hi)⟩

end
end StatMech.FrontierD
