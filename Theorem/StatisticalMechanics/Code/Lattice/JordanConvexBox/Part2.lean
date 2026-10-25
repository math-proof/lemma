/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanConvexBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PathVisitsRow.Part2
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.ArcMonotonise
import Def.StatisticalMechanics.Code.Lattice.JordanConvexBox
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem jcb_separatingSide_of_vCrossing {P : Set (Site 2)} {α β m m' c d : ℤ}
    (hαm : α ≤ m) (hm'β : m' < β) (hcd : c ≤ d) (col : ℤ → ℤ)
    (hlo : ∀ r, c ≤ r → r ≤ d → m ≤ col r)
    (hhi : ∀ r, c ≤ r → r ≤ d → col r ≤ m')
    (hon : ∀ r, c ≤ r → r ≤ d → jsi_cell (col r) r ∈ P)
    (hcorner : ∀ r, c < r → r ≤ d → jsi_cell (col (r - 1)) r ∈ P)
    (hc1 : col (c - 1) = col c)
    (hshift : ∀ r : ℤ,
      col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1) :
    ArcSeparatingSet P α β c d :=
  jsi_separatingSide hαm hm'β
    (jcb_monotoneArc_of_rowData hcd col hlo hhi hon hcorner hc1 hshift).toJsiRowArc


end Lattice
end StatMech
