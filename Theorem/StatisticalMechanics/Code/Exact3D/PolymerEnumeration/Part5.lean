/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part6


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem supportKey_toFinset {d R : ℕ} (s : Finset (BoundedSite d R)) :
    (supportKey s).toFinset = s.map (BoundedSite.coordinateEmbedding d R) := by
  simp [supportKey]

theorem supportKey_injective {d R : ℕ} :
    Function.Injective (@supportKey d R) := by
  intro s t h
  apply Finset.map_inj.mp
  calc
    s.map (BoundedSite.coordinateEmbedding d R) = (supportKey s).toFinset :=
      (supportKey_toFinset s).symm
    _ = (supportKey t).toFinset := by rw [h]
    _ = t.map (BoundedSite.coordinateEmbedding d R) :=
      supportKey_toFinset t


end BoundedPolymerCase
end
end Exact3D
end StatMech
