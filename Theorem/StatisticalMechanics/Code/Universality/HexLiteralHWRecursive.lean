/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_exists_extremum (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlo : lo ≤ hi) : ∃ k, HLHRIsExtremum f up lo hi k := by
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image
    (Finset.Icc lo hi) (fun k => hlhr_signed up (f k))
    ⟨lo, Finset.mem_Icc.mpr ⟨le_rfl, hlo⟩⟩
  refine ⟨c, (Finset.mem_Icc.mp hc).1, (Finset.mem_Icc.mp hc).2, ?_⟩
  intro j hjlo hjhi
  exact hmax j (Finset.mem_Icc.mpr ⟨hjlo, hjhi⟩)


end StatMech.Universality
