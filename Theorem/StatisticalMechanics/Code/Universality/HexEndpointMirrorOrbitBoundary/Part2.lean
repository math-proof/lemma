/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthBoundaryWinding.Part4
import Def.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

namespace HexEndpointMirrorOrbitData

variable {I K V : Type*} [Fintype I] [Fintype K]

variable [DecidableEq I] [DecidableEq K] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexEndpointBoundaryCore R h0 D P}

variable (H : HexEndpointMirrorOrbitData (I := I) (K := K) C)


theorem pair_incTerm_sum (i : I) :
    (∑ e ∈ (H.pairs i).piece, D.incTerm e) =
      (1 / 2 : ℂ) * Complex.I *
        ((2 * Real.cos (H.pairs i).angle * (H.pairs i).mass : ℝ) : ℂ) := by
  calc
    (∑ e ∈ (H.pairs i).piece, D.incTerm e) =
        ∑ e ∈ (H.pairs i).piece,
          ((1 / 2 : ℂ) * hexUnit (H.heading e.vtx e.edge)) *
            D.obs (D.mid e.vtx e.edge) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [HexDomain.incTerm, H.hgeom]
    _ = (1 / 2 : ℂ) *
        (∑ e ∈ (H.pairs i).piece,
          hexUnit (H.heading e.vtx e.edge) *
            D.obs (D.mid e.vtx e.edge)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = (1 / 2 : ℂ) * Complex.I *
        ((2 * Real.cos (H.pairs i).angle * (H.pairs i).mass : ℝ) : ℂ) := by
      rw [(H.pairs i).unit_projection]
      ring

theorem fixed_incTerm_sum (k : K) :
    (∑ e ∈ (H.fixed k).piece, D.incTerm e) =
      (1 / 2 : ℂ) * Complex.I * ((H.fixed k).mass : ℂ) := by
  calc
    (∑ e ∈ (H.fixed k).piece, D.incTerm e) =
        ∑ e ∈ (H.fixed k).piece,
          ((1 / 2 : ℂ) * hexUnit (H.heading e.vtx e.edge)) *
            D.obs (D.mid e.vtx e.edge) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [HexDomain.incTerm, H.hgeom]
    _ = (1 / 2 : ℂ) *
        (∑ e ∈ (H.fixed k).piece,
          hexUnit (H.heading e.vtx e.edge) *
            D.obs (D.mid e.vtx e.edge)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = (1 / 2 : ℂ) * Complex.I * ((H.fixed k).mass : ℂ) := by
      rw [(H.fixed k).unit_projection]
      ring

theorem start_incTerm :
    D.incTerm H.startIncidence = -(1 / 2 : ℂ) * Complex.I := by
  rw [HexDomain.incTerm, H.hgeom, H.start_heading, H.start_mid,
    C.start_value, hexStart_hexUnit_four]
  ring


theorem boundarySum_eq :
    D.boundarySum P =
      (1 / 2 : ℂ) * Complex.I * ((H.totalContribution - 1 : ℝ) : ℂ) := by
  unfold HexDomain.boundarySum
  rw [H.boundary_partition,
    Finset.sum_union H.start_orbits_disjoint,
    Finset.sum_singleton,
    Finset.sum_biUnion H.orbits_disjoint,
    H.start_incTerm]
  calc
    -(1 / 2 : ℂ) * Complex.I +
          ∑ o : I ⊕ K, ∑ e ∈ match o with
            | .inl i => (H.pairs i).piece
            | .inr k => (H.fixed k).piece, D.incTerm e =
        -(1 / 2 : ℂ) * Complex.I +
          (∑ i : I, (1 / 2 : ℂ) * Complex.I *
              ((2 * Real.cos (H.pairs i).angle * (H.pairs i).mass : ℝ) : ℂ)) +
          ∑ k : K, (1 / 2 : ℂ) * Complex.I * ((H.fixed k).mass : ℂ) := by
      rw [Fintype.sum_sum_type]
      simp only
      rw [show (∑ i : I, ∑ e ∈ (H.pairs i).piece, D.incTerm e) =
          ∑ i : I, (1 / 2 : ℂ) * Complex.I *
            ((2 * Real.cos (H.pairs i).angle * (H.pairs i).mass : ℝ) : ℂ) by
        apply Finset.sum_congr rfl
        intro i _
        exact H.pair_incTerm_sum i,
        show (∑ k : K, ∑ e ∈ (H.fixed k).piece, D.incTerm e) =
          ∑ k : K, (1 / 2 : ℂ) * Complex.I * ((H.fixed k).mass : ℂ) by
        apply Finset.sum_congr rfl
        intro k _
        exact H.fixed_incTerm_sum k]
      ring
    _ = (1 / 2 : ℂ) * Complex.I *
        ((H.totalContribution - 1 : ℝ) : ℂ) := by
      unfold totalContribution
      push_cast
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring


theorem totalContribution_eq_one : H.totalContribution = 1 := by
  have hraw := D.hexBoundaryRaw P C.interior_sub
  rw [H.boundarySum_eq] at hraw
  have hfac : (1 / 2 : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hz : (((H.totalContribution - 1 : ℝ) : ℂ)) = 0 :=
    (mul_eq_zero.mp hraw).resolve_left hfac
  have hzReal : H.totalContribution - 1 = 0 := by
    exact_mod_cast hz
  linarith


end HexEndpointMirrorOrbitData
end
end StatMech.Universality
