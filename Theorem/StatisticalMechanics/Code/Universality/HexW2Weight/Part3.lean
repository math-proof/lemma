/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Weight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Def.StatisticalMechanics.Code.Universality.HexW2Weight.Part3


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


theorem hexW2_halves_displacement_split (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    hexInfra_stepReSum h0 ts
      = hexInfra_stepReSum (hexW2_lowerHalf a h0 ts).head (hexW2_lowerHalf a h0 ts).turns
        + hexInfra_stepReSum (hexW2_upperHalf a h0 ts).head (hexW2_upperHalf a h0 ts).turns := by
  show hexInfra_stepReSum h0 ts
    = hexInfra_stepReSum h0 (ts.take (hexW2_cutPos h0 ts))
      + hexInfra_stepReSum (h0 + (ts.take (hexW2_cutPos h0 ts)).sum)
          (ts.drop (hexW2_cutPos h0 ts))
  rw [hexW2_displacement_split h0 ts]
  congr 1
  
  rw [hexInfra_headAccum_eq_add_sum h0 (ts.take (hexW2_cutPos h0 ts))]


end StatMech.Universality
