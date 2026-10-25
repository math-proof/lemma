/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Def.StatisticalMechanics.Code.Universality.FrameChangeIso.Part3
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem fci_face_adj_left (a b : ℤ) :
    (hypercubicLattice 2).Adj ![a, b] ![a - 1, b] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

theorem fci_face_adj_right (a b : ℤ) :
    (hypercubicLattice 2).Adj ![a, b] ![a + 1, b] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]


theorem fci_no_frameChangeIso : ¬ ∃ Φ : Site 2 → Site 2, fci_FrameCompat Φ := by
  rintro ⟨Φ, hΦ⟩
  have hL := hΦ ![0, 0] ![0 - 1, 0] (fci_face_adj_left 0 0)
  rw [fdd_dualEdge_leftSide] at hL
  have hR := hΦ ![0, 0] ![0 + 1, 0] (fci_face_adj_right 0 0)
  rw [fdd_dualEdge_rightSide] at hR
  have hmemL : Φ ![0, 0] ∈ s(![(-0 : ℤ), 0], ![-(0 + 1), 0]) := by
    rw [hL]; exact Sym2.mem_mk_left _ _
  have hmemR : Φ ![0, 0] ∈ s(![(-0 : ℤ), 0 + 1], ![-(0 + 1), 0 + 1]) := by
    rw [hR]; exact Sym2.mem_mk_left _ _
  have h1 : (Φ ![0, 0]) 1 = 0 := by
    rw [Sym2.mem_iff] at hmemL
    rcases hmemL with h | h <;> rw [h] <;> simp
  have h2 : (Φ ![0, 0]) 1 = 1 := by
    rw [Sym2.mem_iff] at hmemR
    rcases hmemR with h | h <;> rw [h] <;> simp
  rw [h1] at h2; exact absurd h2 (by norm_num)


theorem fci_no_open_dual_relabel :
    ¬ ∃ Φ : Site 2 → Site 2, ∀ (f g : Site 2), (hypercubicLattice 2).Adj f g →
      sharedPrimalEdge f g = s(rot90Inv (Φ f), rot90Inv (Φ g)) := by
  rintro ⟨Φ, hΦ⟩
  refine fci_no_frameChangeIso ⟨fun x => Φ x, ?_⟩
  intro f g hadj
  rw [hΦ f g hadj, crossEdge_mk]
  
  rw [show rot90Fun (rot90Inv (Φ f)) = Φ f from rot90Equiv.right_inv (Φ f),
     show rot90Fun (rot90Inv (Φ g)) = Φ g from rot90Equiv.right_inv (Φ g)]


end Universality
end StatMech
