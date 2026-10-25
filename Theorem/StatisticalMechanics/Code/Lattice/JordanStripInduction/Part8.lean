/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part3
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Structure.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part2
open Set SimpleGraph MeasureTheory


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem jsi_monotoneArc_walk {P : Set (Site 2)} {m m' c d : ℤ} (A : JsiMonotoneArc P m m' c d) :
    ∃ (n : ℕ) (W : (hypercubicLattice 2).Walk (jsi_cell (A.col c) c) (jsi_cell (A.col (c + n)) (c + n))),
      c + (n : ℤ) = d ∧ (∀ z ∈ W.support, z ∈ P) := by
  classical
  have hcd : c ≤ d := A.cd
  
  refine ⟨(d - c).toNat, jsi_arcWalk A.col A.shift_all c (d - c).toNat, by omega, ?_⟩
  intro z hz
  
  refine jsi_arcWalk_support_subset P A.col A.shift_all c (d - c).toNat ?_ ?_ z hz
  · 
    intro j hj
    have hjn : (j : ℤ) ≤ (d - c).toNat := by exact_mod_cast hj
    have hjd : c + (j : ℤ) ≤ d := by omega
    exact A.on_arc (jsi_cell (A.col (c + j)) (c + j)) (by simp only [jsi_cell_1]; omega)
      (by simp only [jsi_cell_1]; omega) (by simp)
      (A.band_lo (c + j) (by omega) hjd) (A.band_hi (c + j) (by omega) hjd)
  · 
    intro j hj
    have hjn : (j : ℤ) < (d - c).toNat := by exact_mod_cast hj
    have hjd : c + (j : ℤ) + 1 ≤ d := by omega
    exact A.corner (jsi_cell (A.col (c + j)) (c + j + 1)) (by simp only [jsi_cell_1]; omega)
      (by simp only [jsi_cell_1]; omega) (by simp)
      (A.band_lo (c + j) (by omega) (by omega)) (A.band_hi (c + j) (by omega) (by omega))


theorem jsi_separatingSide {P : Set (Site 2)} {α β m m' c d : ℤ}
    (hαm : α ≤ m) (hm'β : m' < β) (A : JsiRowArc P m m' c d) :
    ArcSeparatingSet P α β c d :=
  jsi_arcSeparatingSet hαm hm'β A


theorem jsi_separatingSideLt {P : Set (Site 2)} {α β m m' c d : ℤ}
    (hαm : α < m) (hm'β : m' ≤ β) (A : JsiRowArc P m m' c d) :
    ArcSeparatingSet P α β c d :=
  jsi_arcSeparatingSetLt hαm hm'β A


end Lattice
end StatMech
