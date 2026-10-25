/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDefectClassify.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusComparison
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

noncomputable def triHexTorusTopologicalCorrectionLogDensity
    (q : ℝ)
    (omega : ∀ L : ℕ, ConfigSpace (Sym2 (TorusSite L)))
    (n : ℕ) : ℝ := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by simp [L]⟩
  exact |Real.log (q ^ triHexTorusDefect L
    (FK.openSub (triangularTorusGraph L) (omega L)))| / (L ^ 2 : ℕ)


end PeriodicPlanar
end FK
end StatMech
