/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxReduce.Part2
import Theorem.StatisticalMechanics.Code.FK.DisjointGraphFactorizeClose.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.FK.CrossBoxGeneralKeystone.Part2
open MeasureTheory Filter Topology Set SimpleGraph
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}


noncomputable def cbk_shiftBoxVert {N r : ℕ} (v : Site d) (hv : flc_vrad v ≤ r)
    (a : boxVerts d N) : boxVerts d (N + r) :=
  ⟨v + (a : Site d), by
    intro i
    have ha : ((a : Site d) i).natAbs ≤ N := a.2 i
    have hvi : (v i).natAbs ≤ flc_vrad v := flc_vrad_le v i
    have : ((v + (a : Site d)) i) = v i + (a : Site d) i := by simp [Pi.add_apply]
    rw [this]
    calc (v i + (a : Site d) i).natAbs ≤ (v i).natAbs + ((a : Site d) i).natAbs :=
          Int.natAbs_add_le _ _
      _ ≤ flc_vrad v + N := Nat.add_le_add hvi ha
      _ ≤ N + r := by omega⟩


noncomputable def cbk_shiftEdge {N r : ℕ} (v : Site d) (hv : flc_vrad v ≤ r) :
    Sym2 (boxVerts d N) → Sym2 (boxVerts d (N + r)) :=
  Sym2.map (cbk_shiftBoxVert v hv)


end FK
end StatMech
