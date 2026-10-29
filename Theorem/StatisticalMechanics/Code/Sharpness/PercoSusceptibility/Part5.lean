/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BKFirstExit
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Def.StatisticalMechanics.Code.Sharpness.PercoSusceptibility.Part5
open MeasureTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators Topology


namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem shk_withinBoxEvent_mono (x : Site d) :
    Monotone (fun n : ℕ =>
      connWithinEvent d (box d n) (origin d) x) := by
  intro m n hmn omega homega
  obtain ⟨h0m, hxm, hconn⟩ := homega
  have hsub : box d m ⊆ box d n := box_mono d hmn
  exact ⟨hsub h0m, hsub hxm,
    connectedWithin_mono_set' omega hsub hconn⟩


theorem shk_connected_iff_mem_iUnion_withinBox (omega : ConfigSpace (Sym2 (Site d)))
    (x : Site d) :
    Connected d omega (origin d) x ↔
      omega ∈ ⋃ n : ℕ, connWithinEvent d (box d n) (origin d) x := by
  constructor
  · intro hconn
    obtain ⟨w⟩ := hconn
    obtain ⟨n, hn⟩ := finset_subset_box_su w.support.toFinset
    have hw : ∀ z ∈ w.support, z ∈ box d n := by
      intro z hz
      exact hn (by simpa using hz)
    have h0 : origin d ∈ box d n := hw _ w.start_mem_support
    have hx : x ∈ box d n := hw _ w.end_mem_support
    refine Set.mem_iUnion.mpr ⟨n, h0, hx, ?_⟩
    exact walk_induce_reachable (openSubgraph d omega) (box d n) w hw h0 hx
  · intro hmem
    obtain ⟨n, h0, hx, hconn⟩ := Set.mem_iUnion.mp hmem
    exact hconn.connected


theorem shk_connWithinBox_tendsto_twoPoint (p : NNReal) (hp : p ≤ 1)
    (x : Site d) :
    Tendsto (fun n =>
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (connWithinEvent d (box d n) (origin d) x))
      atTop (nhds (shk_twoPointProb p hp x)) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site d)) p hp
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (shk_withinBoxEvent_mono (d := d) x)
  have hreal := (ENNReal.tendsto_toReal
    (measure_ne_top mu (⋃ n : ℕ, connWithinEvent d (box d n) (origin d) x))).comp hmeasure
  have hunion : (⋃ n : ℕ, connWithinEvent d (box d n) (origin d) x) =
      {omega | Connected d omega (origin d) x} := by
    ext omega
    exact (shk_connected_iff_mem_iUnion_withinBox omega x).symm
  rw [hunion] at hreal
  simpa only [Function.comp_apply, Measure.real, shk_twoPointProb, mu] using hreal


theorem shk_twoPoint_partialSum_le (p : NNReal) (hp : p ≤ 1)
    (S : Finset (Site d)) (h0S : origin d ∈ S)
    (hphi : phi d p hp S < 1) (T : Finset (Site d)) :
    ∑ x ∈ T, shk_twoPointProb p hp x ≤
      (S.card : ℝ) / (1 - phi d p hp S) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site d)) p hp
  let f : ℕ → Site d → ℝ := fun n x =>
    mu.real (connWithinEvent d (box d n) (origin d) x)
  have hlim : Tendsto (fun n => ∑ x ∈ T, f n x) atTop
      (nhds (∑ x ∈ T, shk_twoPointProb p hp x)) := by
    exact tendsto_finsetSum T fun x _ =>
      shk_connWithinBox_tendsto_twoPoint p hp x
  obtain ⟨N, hTN⟩ := finset_subset_box_su T
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop N] with n hn
  have hTbox : T ⊆ boxFinset d n := by
    intro x hx
    apply mem_boxFinset.mpr
    exact box_mono d hn (hTN (by simpa using hx))
  have hboxcoe : (boxFinset d n : Set (Site d)) = box d n := by
    ext x
    simp only [Finset.mem_coe, mem_boxFinset]
  calc
    (∑ x ∈ T, f n x) ≤ ∑ x ∈ boxFinset d n, f n x :=
      Finset.sum_le_sum_of_subset_of_nonneg hTbox
        (fun x _ _ => measureReal_nonneg)
    _ = shk_restrictedSusceptibility p hp (boxFinset d n) (origin d) := by
      simp only [f, mu, shk_restrictedSusceptibility,
        shk_connEvent_singleton_eq_connWithinEvent, hboxcoe]
    _ ≤ (S.card : ℝ) / (1 - phi d p hp S) :=
      shk_restrictedSusceptibility_le p hp S (boxFinset d n) h0S
        (mem_boxFinset.mpr (origin_mem_box' n)) hphi


theorem shk_twoPoint_summable_of_phi_lt_one (p : NNReal) (hp : p ≤ 1)
    (S : Finset (Site d)) (h0S : origin d ∈ S)
    (hphi : phi d p hp S < 1) :
    Summable (shk_twoPointProb (d := d) p hp) := by
  apply summable_of_sum_le (fun _ => measureReal_nonneg)
  exact shk_twoPoint_partialSum_le p hp S h0S hphi


theorem finite_susceptibility_of_lt_tildeBetaCPerco {beta : ℝ}
    (hbeta : beta < tildeBetaCPerco d) :
    ∃ S : Finset (Site d),
      origin d ∈ S ∧
      phiBeta d beta S < 1 ∧
      Summable (shk_twoPointProb (d := d) (bondParam beta)
        (bondParam_le_one beta)) ∧
      ∀ Lam : Finset (Site d), origin d ∈ Lam →
        shk_restrictedSusceptibility (bondParam beta)
            (bondParam_le_one beta) Lam (origin d) ≤
          (S.card : ℝ) / (1 - phiBeta d beta S) := by
  obtain ⟨S, h0S, hphi⟩ :=
    exists_phiBeta_witness_of_lt_tildeBetaCPerco hbeta
  refine ⟨S, h0S, hphi, ?_, ?_⟩
  · exact shk_twoPoint_summable_of_phi_lt_one (bondParam beta)
      (bondParam_le_one beta) S h0S hphi
  · intro Lam h0Lam
    exact shk_restrictedSusceptibility_le (bondParam beta)
      (bondParam_le_one beta) S Lam h0S h0Lam hphi

end Sharpness
end StatMech
