/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricScatteringBound.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricCovering
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexNegativeHalfRootPartition
    {m : Nat} (q : Fin m → Real) (hm : 0 < m) (k : Nat) : Real :=
  if hk : k < m then -q ⟨m - 1 - k, by omega⟩ else q ⟨0, hm⟩

end
end StatMech.FrontierD
