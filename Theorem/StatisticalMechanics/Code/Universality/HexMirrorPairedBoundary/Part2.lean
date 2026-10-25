/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexGenuineStripPhaseObstruction
import Def.StatisticalMechanics.Code.Universality.HexMirrorPairedBoundary.Part2


namespace StatMech.Universality

open Complex Set

open scoped BigOperators


namespace HexFiniteStripMirrorPairedData

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexFiniteStripBoundaryCore R h0 D P}


theorem pair_incTerm_sum
    (H : HexFiniteStripMirrorPairedData (ι := ι) C) (i : ι) :
    (∑ e ∈ (H.pairs i).piece, D.incTerm e) =
      (1 / 2 : ℂ) * Complex.I *
        ((2 * Real.cos (H.pairs i).angle * (H.pairs i).mass : ℝ) : ℂ) := by
  calc
    (∑ e ∈ (H.pairs i).piece, D.incTerm e) =
        ∑ e ∈ (H.pairs i).piece,
          ((1 / 2 : ℂ) * hexUnit (H.heading e.vtx e.edge)) *
            D.obs (D.mid e.vtx e.edge) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [HexDomain.incTerm, H.hgeom]
    _ = (1 / 2 : ℂ) *
        (∑ e ∈ (H.pairs i).piece,
          hexUnit (H.heading e.vtx e.edge) *
            D.obs (D.mid e.vtx e.edge)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring
    _ = (1 / 2 : ℂ) * Complex.I *
        ((2 * Real.cos (H.pairs i).angle * (H.pairs i).mass : ℝ) : ℂ) := by
      rw [(H.pairs i).unit_projection]
      ring


theorem start_incTerm
    (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
    D.incTerm H.startIncidence =
      -(1 / 2 : ℂ) * Complex.I * (C.Fa : ℂ) := by
  rw [HexDomain.incTerm, H.hgeom, H.start_heading, H.start_mid, ← C.Fa_eq,
    hexStart_hexUnit_four]
  ring


theorem boundarySum_eq
    (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
    D.boundarySum P =
      (1 / 2 : ℂ) * Complex.I *
        ((H.pairedContribution - C.Fa : ℝ) : ℂ) := by
  unfold HexDomain.boundarySum
  rw [H.boundary_partition,
    Finset.sum_union H.start_pairs_disjoint,
    Finset.sum_singleton,
    Finset.sum_biUnion H.pairs_disjoint,
    H.start_incTerm]
  calc
    -(1 / 2 : ℂ) * Complex.I * (C.Fa : ℂ) +
          ∑ i : ι, ∑ e ∈ (H.pairs i).piece, D.incTerm e =
        -(1 / 2 : ℂ) * Complex.I * (C.Fa : ℂ) +
          ∑ i : ι, (1 / 2 : ℂ) * Complex.I *
            ((2 * Real.cos (H.pairs i).angle *
              (H.pairs i).mass : ℝ) : ℂ) := by
      apply congrArg
      apply Finset.sum_congr rfl
      intro i hi
      exact H.pair_incTerm_sum i
    _ = (1 / 2 : ℂ) * Complex.I *
        ((H.pairedContribution - C.Fa : ℝ) : ℂ) := by
      unfold pairedContribution
      push_cast
      rw [← Finset.mul_sum]
      ring


theorem pairedContribution_eq_Fa
    (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
    H.pairedContribution = C.Fa := by
  have hraw := D.hexBoundaryRaw P C.interior_sub
  rw [H.boundarySum_eq] at hraw
  have hfac : (1 / 2 : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hz : (((H.pairedContribution - C.Fa : ℝ) : ℂ)) = 0 :=
    (mul_eq_zero.mp hraw).resolve_left hfac
  have hzReal : H.pairedContribution - C.Fa = 0 := by
    exact_mod_cast hz
  linarith


theorem normalized_real_boundary_contribution
    (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
    hexChi⁻¹ * H.pairedContribution = 1 := by
  rw [H.pairedContribution_eq_Fa, C.Fa_eq_hexChi]
  exact inv_mul_cancel₀ (ne_of_gt hexChi_pos)

end HexFiniteStripMirrorPairedData
end StatMech.Universality
