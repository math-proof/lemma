/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace PolymerSupport

instance instDecidableEq (d : ℕ) : DecidableEq (PolymerSupport d) := by
  intro P Q
  cases P with
  | mk Pc =>
    cases Q with
    | mk Qc =>
      by_cases h : Pc = Qc
      · exact isTrue (by cases h; rfl)
      · exact isFalse (by intro hPQ; cases hPQ; exact h rfl)


end PolymerSupport
end
end Exact3D
end StatMech
