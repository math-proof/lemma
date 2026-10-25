/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperPeierls
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
import Theorem.StatisticalMechanics.Code.FK.Ergodicity
import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Theorem.StatisticalMechanics.Code.Probability.InfiniteBK
import Def.StatisticalMechanics.Code.Percolation.PcUpperViaFK.Part3
open MeasureTheory Filter Topology Set Finset
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.FK

variable {d : ℕ}


theorem bernoulliProduct_map_planeRestrict (k : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (pcv_planeRestrict k)
        (bernoulliProductMeasure (E := Sym2 (Site (2 + k))) p hp) =
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp := by
  exact bernoulliProduct_map_injective_restrict p hp (pcv_edgeEmbed k)
    (pcv_edgeEmbed_injective k)

@[simp] theorem pcv_siteEmbed_origin (k : ℕ) :
    pcv_siteEmbed k (origin 2) = origin (2 + k) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [origin]


theorem pcv_connected_of_planeRestrict (k : ℕ)
    (omega : ConfigSpace (Sym2 (Site (2 + k)))) {x y : Site 2}
    (h : Lattice.Connected 2 (pcv_planeRestrict k omega) x y) :
    Lattice.Connected (2 + k) omega (pcv_siteEmbed k x) (pcv_siteEmbed k y) := by
  let f : openSubgraph 2 (pcv_planeRestrict k omega) →g openSubgraph (2 + k) omega :=
    { toFun := pcv_siteEmbed k
      map_rel' := by
        intro u v huv
        simp only [openSubgraph_adj] at huv ⊢
        refine ⟨(pcv_siteEmbed_adj_iff k u v).2 huv.1, ?_⟩
        simpa [pcv_planeRestrict, pcv_edgeEmbed] using huv.2 }
  exact h.map f


theorem pcv_plane_percolation_subset (k : ℕ) :
    pcv_planeRestrict k ⁻¹' percolationEvent 2 ⊆ percolationEvent (2 + k) := by
  intro omega hperco
  change pcv_planeRestrict k omega ∈ percolationEvent 2 at hperco
  rw [mem_percolationEvent] at hperco ⊢
  have himg : (pcv_siteEmbed k '' cluster 2 (pcv_planeRestrict k omega) (origin 2)).Infinite :=
    hperco.image (pcv_siteEmbed_injective k).injOn
  apply himg.mono
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_cluster] at hx ⊢
  simpa using pcv_connected_of_planeRestrict k omega hx


theorem theta_two_le_theta_add (k : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    theta 2 p hp ≤ theta (2 + k) p hp := by
  let mud := bernoulliProductMeasure (E := Sym2 (Site (2 + k))) p hp
  let mu2 := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  have hpres : MeasurePreserving (pcv_planeRestrict k) mud mu2 :=
    ⟨measurable_pi_lambda _ fun _ => measurable_pi_apply _,
      bernoulliProduct_map_planeRestrict k p hp⟩
  have hpre := hpres.measureReal_preimage
    (frp_measurableSet_percolationEvent 2).nullMeasurableSet
  unfold theta
  rw [← hpre]
  exact measureReal_mono (pcv_plane_percolation_subset k)


theorem theta_mono_parameter {p q : ℝ≥0} (hp : p ≤ 1) (hq : q ≤ 1)
    (hpq : p ≤ q) : theta d p hp ≤ theta d q hq := by
  let mup := bernoulliProductMeasure (E := Sym2 (Site d)) p hp
  let muq := bernoulliProductMeasure (E := Sym2 (Site d)) q hq
  have hplim := boxBdryConnEvent_real_tendsto_percolation (d := d) mup
  have hqlim := boxBdryConnEvent_real_tendsto_percolation (d := d) muq
  apply le_of_tendsto_of_tendsto
    (by simpa only [theta, mup] using hplim)
    (by simpa only [theta, muq] using hqlim)
  apply Filter.Eventually.of_forall
  intro n
  let A : Set (ConfigSpace (Sym2 (boxVerts d n))) :=
    {omega | IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega
      (IsingFK.boxOrigin d n)}
  have hAdep : StatMech.DependsOn A
      ((Finset.univ : Finset (Sym2 (boxVerts d n))) : Set _) := by
    intro omega omega' heq
    have homega : omega = omega' := by
      funext e
      exact (heq e (by simp)).symm
    subst omega'
    rfl
  have hmono := ibk_measure_mono_parameter hp hq hpq Finset.univ hAdep
    (isIncreasing_connToBdryEvent n)
  change (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
      (boxBdryConnEvent d n) ≤
    (bernoulliProductMeasure (E := Sym2 (Site d)) q hq).real
      (boxBdryConnEvent d n)
  simpa only [show boxBdryConnEvent d n = boxRestrict d n ⁻¹' A from rfl,
    bernoulliProduct_boxRestrict_preimage] using hmono


theorem pc_le_of_theta_pos (p : ℝ≥0) (hp : p ≤ 1)
    (hpos : 0 < theta d p hp) : pc d ≤ p := by
  unfold pc
  apply csSup_le'
  intro q hq
  obtain ⟨hq1, hqzero⟩ := hq
  by_contra hnot
  have hpq : p ≤ q := le_of_not_ge hnot
  have hmono := theta_mono_parameter (d := d) hp hq1 hpq
  rw [hqzero] at hmono
  exact (not_lt_of_ge hmono) hpos


theorem exists_theta_two_pos_below_one :
    ∃ (p : ℝ≥0) (hp1 : p < 1), 0 < theta 2 p hp1.le := by
  obtain ⟨beta, hbeta, hmag⟩ := IsingFK.pup_exists_positive_magnetization
  have hp0r : 0 < IsingFK.pOfBeta beta := Ising.pOfBeta_pos hbeta
  have hp1r : IsingFK.pOfBeta beta < 1 := Ising.pOfBeta_lt_one beta
  let p : ℝ≥0 := ⟨IsingFK.pOfBeta beta, hp0r.le⟩
  have hp0 : 0 < p := by exact_mod_cast hp0r
  have hp1 : p < 1 := by exact_mod_cast hp1r
  have hid : Ising.magnetization 2 beta =
      fkTheta 2 hp0r hp1r (by norm_num : (0 : ℝ) < 2) (q := 2) :=
    Ising.mfc_magPercoId 2 (by norm_num) (IsingFK.hbx_hisingBox 2)
      beta hbeta hp0r hp1r
  have hfk : 0 < fkTheta 2 hp0r hp1r (by norm_num : (0 : ℝ) < 2) (q := 2) := by
    rwa [← hid]
  have htheta : 0 < theta 2 p hp1.le :=
    lt_of_lt_of_le hfk (fkTheta_two_le_bernoulliTheta p hp0 hp1)
  exact ⟨p, hp1, htheta⟩


theorem pc_two_lt_one_via_fk : pc 2 < 1 := by
  obtain ⟨p, hp1, htheta⟩ := exists_theta_two_pos_below_one
  exact lt_of_le_of_lt (pc_le_of_theta_pos p hp1.le htheta) hp1


theorem pc_two_nontrivial : 0 < pc 2 ∧ pc 2 < 1 :=
  ⟨pc_pos (by norm_num), pc_two_lt_one_via_fk⟩


theorem pc_lt_one_of_two_le_via_fk {d : ℕ} (hd : 2 ≤ d) : pc d < 1 := by
  obtain ⟨p, hp1, htheta2⟩ := exists_theta_two_pos_below_one
  have htheta : 0 < theta (2 + (d - 2)) p hp1.le :=
    lt_of_lt_of_le htheta2 (theta_two_le_theta_add (d - 2) p hp1.le)
  rw [Nat.add_sub_of_le hd] at htheta
  exact lt_of_le_of_lt (pc_le_of_theta_pos p hp1.le htheta) hp1


theorem pc_nontrivial_of_two_le {d : ℕ} (hd : 2 ≤ d) :
    0 < pc d ∧ pc d < 1 :=
  ⟨pc_pos (by omega), pc_lt_one_of_two_le_via_fk hd⟩

end Percolation
end StatMech
