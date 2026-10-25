/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part6
import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem kif_kingAdj_left (x y : ℤ) : mci_kingGraph.Adj (![x, y] : Site 2) ![x - 1, y] := by
  refine ⟨by simp, by simp, ?_⟩
  intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega


theorem kif_kingAdj_down (x y : ℤ) : mci_kingGraph.Adj (![x, y] : Site 2) ![x, y - 1] := by
  refine ⟨by simp, by simp, ?_⟩
  intro h; have := congrFun h 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at this; omega


theorem kif_kingAdj_right (x y : ℤ) : mci_kingGraph.Adj (![x, y] : Site 2) ![x + 1, y] := by
  refine ⟨by simp, by simp, ?_⟩
  intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega


end Lattice
end StatMech
