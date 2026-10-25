/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Theorem.StatisticalMechanics.Code.Ising.PressureSurfaceVolume.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangLogDerivativeBound.Part2
import Def.StatisticalMechanics.Code.FrontierA.LeeYangBoxPressure
open scoped BigOperators
open Finset Filter Topology Set SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Sharpness


variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ising_vanHove_none_vertex_card (d m n : ℕ) :
    Fintype.card {x : boxVerts d n // ecz_vanHoveTag m n x = none} +
        (ecz_T m n) ^ d * Fintype.card (boxVerts d m) = Fintype.card (boxVerts d n) := by
  have htotal : Fintype.card (boxVerts d n) =
      ∑ tau : Option (Fin d → Fin (ecz_T m n)),
        Fintype.card {x : boxVerts d n // ecz_vanHoveTag m n x = tau} := by
    calc
      Fintype.card (boxVerts d n) =
          Fintype.card ((tau : Option (Fin d → Fin (ecz_T m n))) ×
            {x : boxVerts d n // ecz_vanHoveTag m n x = tau}) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv (ecz_vanHoveTag m n)).symm
      _ = _ := Fintype.card_sigma
  rw [Fintype.sum_option] at htotal
  have heach : ∀ c : Fin d → Fin (ecz_T m n),
      Fintype.card {x : boxVerts d n // ecz_vanHoveTag m n x = some c} =
        Fintype.card (boxVerts d m) := fun c =>
    (Fintype.card_congr (ecz_cellEquiv m n c)).symm
  rw [Finset.sum_congr rfl (fun c _ => heach c), Finset.sum_const,
    Finset.card_univ, ecz_cell_card, nsmul_eq_mul] at htotal
  exact htotal.symm

theorem isingZ_cellBlock (d m n : ℕ) (c : Fin d → Fin (ecz_T m n))
    (beta h : ℝ) :
    isingZ (qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c)) beta h =
      isingZ (boxGraph d m) beta h := by
  exact (isingZ_relabel (boxGraph d m)
    (qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c))
    (ecz_cellBlockIso m n c).toEquiv
    (fun x y => (ecz_cellBlockIso m n c).map_rel_iff.symm) beta h).symm


theorem isingBoxLogZ_vanHove_abs_le (d m n : ℕ) (beta h : ℝ) :
    |isingBoxLogZ d beta h n - ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m| ≤
      (Real.log 2 + |beta| * |h|) *
          ((Fintype.card (boxVerts d n) : ℝ) -
            ((ecz_T m n) ^ d : ℝ) * Fintype.card (boxVerts d m)) +
        |beta| * (((boxGraph d n).edgeFinset.card : ℝ) -
          ((ecz_T m n) ^ d : ℝ) * (boxGraph d m).edgeFinset.card) := by
  classical
  let tag : boxVerts d n → Option (Fin d → Fin (ecz_T m n)) :=
    ecz_vanHoveTag (d := d) m n
  obtain ⟨I, hpeel, hcard⟩ :=
    isingLogZ_tagPeel (boxGraph d n) tag beta h Finset.univ
  have hrest : isingZ (qp_restG (boxGraph d n) tag Finset.univ) beta h =
      isingZ (boxGraph d n) beta h := by
    exact isingZ_relabel _ _ (ecz_restUnivIso m n).toEquiv
      (fun x y => (ecz_restUnivIso m n).map_rel_iff.symm) beta h
  let N := qp_blkG (boxGraph d n) tag none
  have hsumZ : (∑ tau ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
      Real.log (isingZ (qp_blkG (boxGraph d n) tag tau) beta h)) =
      Real.log (isingZ N beta h) +
        ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m := by
    rw [show (∑ tau ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        Real.log (isingZ (qp_blkG (boxGraph d n) tag tau) beta h)) =
      ∑ tau : Option (Fin d → Fin (ecz_T m n)),
        Real.log (isingZ (qp_blkG (boxGraph d n) tag tau) beta h) from rfl,
      Fintype.sum_option]
    congr 1
    rw [Finset.sum_congr rfl (fun c _ => by rw [isingZ_cellBlock d m n c]),
      Finset.sum_const, Finset.card_univ, ecz_cell_card, nsmul_eq_mul]
    push_cast
    rfl
  have hsumE : I + N.edgeFinset.card +
      (ecz_T m n) ^ d * (boxGraph d m).edgeFinset.card =
        (boxGraph d n).edgeFinset.card := by
    rw [show (∑ tau ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        (qp_blkG (boxGraph d n) tag tau).edgeFinset.card) =
      ∑ tau : Option (Fin d → Fin (ecz_T m n)),
        (qp_blkG (boxGraph d n) tag tau).edgeFinset.card from rfl,
      Fintype.sum_option] at hcard
    rw [Finset.sum_congr rfl (fun c _ => ecz_cellBlock_edge_card m n c),
      Finset.sum_const, Finset.card_univ, ecz_cell_card, nsmul_eq_mul] at hcard
    have hrestE := (ecz_restUnivIso (d := d) m n).card_edgeFinset_eq
    change (qp_restG (boxGraph d n) tag Finset.univ).edgeFinset.card =
      (boxGraph d n).edgeFinset.card at hrestE
    simpa [tag, N, hrestE, Nat.add_assoc] using hcard
  let VN := Fintype.card {x : boxVerts d n // tag x = none}
  have hsumV : VN + (ecz_T m n) ^ d * Fintype.card (boxVerts d m) =
      Fintype.card (boxVerts d n) := by
    simpa [tag, VN] using ising_vanHove_none_vertex_card d m n
  have hNbound := isingLogZ_abs_le N beta h
  rw [hrest, hsumZ] at hpeel
  change |isingBoxLogZ d beta h n -
      (Real.log (isingZ N beta h) +
        ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m)| ≤ |beta| * I at hpeel
  have htri : |isingBoxLogZ d beta h n -
      ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m| ≤
      |beta| * I + |Real.log (isingZ N beta h)| := by
    calc
      |isingBoxLogZ d beta h n -
          ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m| =
          |(isingBoxLogZ d beta h n -
              (Real.log (isingZ N beta h) +
                ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m)) +
            Real.log (isingZ N beta h)| := by congr 1 <;> ring
      _ ≤ |isingBoxLogZ d beta h n -
              (Real.log (isingZ N beta h) +
                ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m)| +
            |Real.log (isingZ N beta h)| := abs_add_le _ _
      _ ≤ |beta| * I + |Real.log (isingZ N beta h)| := by
        simpa using add_le_add_right hpeel |Real.log (isingZ N beta h)|
  have hVN : Fintype.card {x : boxVerts d n // tag x = none} = VN := rfl
  change |Real.log (isingZ N beta h)| ≤
    (VN : ℝ) * Real.log 2 +
      |beta| * ((N.edgeFinset.card : ℝ) + |h| * VN) at hNbound
  have hsumER : (I : ℝ) + (N.edgeFinset.card : ℝ) +
      ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) =
        ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hsumE
  have hsumVR : (VN : ℝ) + ((ecz_T m n) ^ d : ℝ) *
      (Fintype.card (boxVerts d m) : ℝ) =
        (Fintype.card (boxVerts d n) : ℝ) := by exact_mod_cast hsumV
  calc
    |isingBoxLogZ d beta h n -
        ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m| ≤
        |beta| * I + |Real.log (isingZ N beta h)| := htri
    _ ≤ |beta| * I + ((VN : ℝ) * Real.log 2 +
      |beta| * ((N.edgeFinset.card : ℝ) + |h| * VN)) :=
        by simpa using add_le_add_left hNbound (|beta| * (I : ℝ))
    _ = (Real.log 2 + |beta| * |h|) *
          ((Fintype.card (boxVerts d n) : ℝ) -
            ((ecz_T m n) ^ d : ℝ) * Fintype.card (boxVerts d m)) +
        |beta| * (((boxGraph d n).edgeFinset.card : ℝ) -
          ((ecz_T m n) ^ d : ℝ) * (boxGraph d m).edgeFinset.card) := by
      rw [← hsumVR, ← hsumER]
      ring


theorem isingBox_vertexBulkFraction_tendsto (d m : ℕ) :
    Tendsto (fun n =>
      ((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
        (Fintype.card (boxVerts d n) : ℝ)) atTop (nhds 1) := by
  have h := (ecz_packing_ratio_tendsto m).pow d
  convert h using 1
  · funext n
    rw [ecz_boxVerts_card, ecz_boxVerts_card]
    push_cast
    rw [div_pow, mul_pow]
  · simp

theorem isingBox_edge_div_vertex_eq (d n : ℕ) (hd : 1 ≤ d) :
    ((boxGraph d n).edgeFinset.card : ℝ) /
        (Fintype.card (boxVerts d n) : ℝ) =
      (d : ℝ) * (2 * (n : ℝ)) / (2 * n + 1) := by
  rw [EdgeCount.boxGraph_edgeCard d n hd, ecz_boxVerts_card]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  push_cast
  have hside : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

theorem isingBox_edgeDensity_tendsto (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n => ((boxGraph d n).edgeFinset.card : ℝ) /
      (Fintype.card (boxVerts d n) : ℝ)) atTop (nhds (d : ℝ)) := by
  have hden : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) atTop atTop :=
    ecz_denom_tendsto_atTop
  have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / (2 * n + 1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hratio : Tendsto (fun n : ℕ => (2 * (n : ℝ)) / (2 * n + 1))
      atTop (nhds 1) := by
    have h := hzero.const_sub 1
    convert h using 1
    · funext n
      have hn : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    · simp
  have hmul := (tendsto_const_nhds (x := (d : ℝ))).mul hratio
  convert hmul using 1
  · funext n
    rw [isingBox_edge_div_vertex_eq d n hd]
    ring
  · simp

theorem isingBox_bulkEdgeDensity_tendsto (d m : ℕ) :
    Tendsto (fun n =>
      ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) /
        (Fintype.card (boxVerts d n) : ℝ)) atTop
      (nhds (((boxGraph d m).edgeFinset.card : ℝ) /
        (Fintype.card (boxVerts d m) : ℝ))) := by
  have hVpos : (0 : ℝ) < Fintype.card (boxVerts d m) := by
    rw [ecz_boxVerts_card]
    positivity
  have h := (isingBox_vertexBulkFraction_tendsto d m).mul
    (tendsto_const_nhds (x := ((boxGraph d m).edgeFinset.card : ℝ) /
      (Fintype.card (boxVerts d m) : ℝ)))
  convert h using 1
  · funext n
    field_simp [ne_of_gt hVpos]
  · field_simp [ne_of_gt hVpos]

theorem isingBox_edgeDeficitDensity_tendsto (d m : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n =>
      (((boxGraph d n).edgeFinset.card : ℝ) -
        ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) /
          (Fintype.card (boxVerts d n) : ℝ)) atTop
      (nhds ((d : ℝ) - ((boxGraph d m).edgeFinset.card : ℝ) /
        (Fintype.card (boxVerts d m) : ℝ))) := by
  have h := (isingBox_edgeDensity_tendsto d hd).sub
    (isingBox_bulkEdgeDensity_tendsto d m)
  convert h using 1
  funext n
  rw [sub_div]

theorem isingBox_edgeSurface_eq (d m : ℕ) (hd : 1 ≤ d) :
    (d : ℝ) - ((boxGraph d m).edgeFinset.card : ℝ) /
        (Fintype.card (boxVerts d m) : ℝ) =
      (d : ℝ) / (2 * (m : ℝ) + 1) := by
  rw [isingBox_edge_div_vertex_eq d m hd]
  have hm : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem isingBox_edgeSurface_tendsto_zero (d : ℕ) :
    Tendsto (fun m : ℕ => (d : ℝ) / (2 * (m : ℝ) + 1)) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop ecz_denom_tendsto_atTop


theorem isingBoxPressure_vanHove_abs_le (d m n : ℕ) (beta h : ℝ) :
    |isingBoxPressureSeq d beta h n -
        (((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
          (Fintype.card (boxVerts d n) : ℝ)) * isingBoxPressureSeq d beta h m| ≤
      (Real.log 2 + |beta| * |h|) *
        (1 - ((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
          (Fintype.card (boxVerts d n) : ℝ)) +
      |beta| * ((((boxGraph d n).edgeFinset.card : ℝ) -
        ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) /
          (Fintype.card (boxVerts d n) : ℝ)) := by
  have hraw := isingBoxLogZ_vanHove_abs_le d m n beta h
  have hVn : (0 : ℝ) < Fintype.card (boxVerts d n) := by
    rw [ecz_boxVerts_card]
    positivity
  have hVm : (0 : ℝ) < Fintype.card (boxVerts d m) := by
    rw [ecz_boxVerts_card]
    positivity
  have hdiv := (div_le_div_iff_of_pos_right hVn).2 hraw
  have heq : isingBoxPressureSeq d beta h n -
      (((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
        (Fintype.card (boxVerts d n) : ℝ)) * isingBoxPressureSeq d beta h m =
      (isingBoxLogZ d beta h n -
        ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m) /
          (Fintype.card (boxVerts d n) : ℝ) := by
    unfold isingBoxPressureSeq
    field_simp [ne_of_gt hVn, ne_of_gt hVm]
  calc
    |isingBoxPressureSeq d beta h n -
        (((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
          (Fintype.card (boxVerts d n) : ℝ)) * isingBoxPressureSeq d beta h m| =
      |isingBoxLogZ d beta h n -
        ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m| /
          (Fintype.card (boxVerts d n) : ℝ) := by
            rw [heq, abs_div, abs_of_pos hVn]
    _ ≤ ((Real.log 2 + |beta| * |h|) *
          ((Fintype.card (boxVerts d n) : ℝ) -
            ((ecz_T m n) ^ d : ℝ) * Fintype.card (boxVerts d m)) +
        |beta| * (((boxGraph d n).edgeFinset.card : ℝ) -
          ((ecz_T m n) ^ d : ℝ) * (boxGraph d m).edgeFinset.card)) /
            (Fintype.card (boxVerts d n) : ℝ) := hdiv
    _ = _ := by
      field_simp [ne_of_gt hVn]

end StatMech.FrontierA
