/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace PolymerSupport

@[simp] theorem mem_translationCandidateSet {d : ℕ}
    (P Q : PolymerSupport d) (v : Site d) :
    v ∈ translationCandidateSet P Q ↔
      ∃ y, y ∈ Q ∧ ∃ x, x ∈ P ∧ y - x = v := by
  classical
  simp [translationCandidateSet]


end PolymerSupport
end
end Exact3D
end StatMech
