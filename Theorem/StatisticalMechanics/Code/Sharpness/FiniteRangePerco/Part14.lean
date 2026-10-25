/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Def.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part14
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


theorem frpCrossingEventFrom_zero (K : FiniteRangeKernel d) (n : ℕ) :
    frpCrossingEventFrom K 0 n = frpCrossingEvent K n := rfl


theorem frpCrossingEventFrom_eq_preimage (K : FiniteRangeKernel d)
    (y : Site d) (n : ℕ) :
    frpCrossingEventFrom K y n =
      (shift (Multiplicative.ofAdd (-y)) : ConfigSpace (Sym2 (Site d)) → _) ⁻¹'
        connEvent (frpGraph K) Set.univ (0 : Site d)
          (frpShiftedBox y n : Set (Site d))ᶜ := by
  ext omega
  set g := Multiplicative.ofAdd (-y) with hg
  have hgy : g • y = (0 : Site d) := by
    funext i
    show -y i + y i = (0 : ℤ)
    ring
  constructor
  · rintro ⟨_, v, _, hvout, hconn⟩
    refine ⟨Set.mem_univ _, g • v, Set.mem_univ _, ?_, ?_⟩
    · rw [Set.mem_compl_iff, Finset.mem_coe, mem_frpShiftedBox]
      have heq : g • v + y = v := by
        funext i
        show (-y i + v i) + y i = v i
        ring
      rwa [heq]
    · have hs := (frp_connWithin_univ_shift K g omega y v).mpr hconn
      rwa [hgy] at hs
  · rintro ⟨_, w, _, hwout, hconn⟩
    refine ⟨Set.mem_univ _, g⁻¹ • w, Set.mem_univ _, ?_, ?_⟩
    · rw [Set.mem_compl_iff, Finset.mem_coe, mem_frpShiftedBox] at hwout
      have hgi : g⁻¹ • w = w + y := by
        funext i
        rw [smul_site_apply]
        simp only [hg, ← ofAdd_neg, toAdd_ofAdd, neg_neg, Pi.add_apply]
        ring
      rwa [hgi]
    · have hs := (frp_connWithin_univ_shift K g omega y (g⁻¹ • w)).mp ?_
      · exact hs
      · rw [hgy, smul_inv_smul]
        exact hconn


theorem frp_crossProbFrom_le (K : FiniteRangeKernel d) (beta : ℝ)
    (y : Site d) {L m n : ℕ} (hy : y ∈ box d L)
    (hmLn : m + L ≤ n) (hm : 1 ≤ m) :
    (frpMeasure K beta).real (frpCrossingEventFrom K y n) ≤
      frpCrossProb K beta m := by
  let mu := frpMeasure K beta
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, frpMeasure]
    infer_instance
  let g := Multiplicative.ofAdd (-y)
  let B := connEvent (frpGraph K) Set.univ (0 : Site d)
    (frpShiftedBox y n : Set (Site d))ᶜ
  have hyinner : y ∈ box d (n - 1) := by
    apply box_mono d (show L ≤ n - 1 by omega)
    exact hy
  have h0B : (0 : Site d) ∈ frpShiftedBox y n := by
    rw [mem_frpShiftedBox]
    simpa using hyinner
  have hBmeas : MeasurableSet B :=
    measurableSet_frp_exitEvent K (frpShiftedBox y n) 0 h0B
  have hpres := (frpMeasure_translationInvariant K beta) g
  have hstep : mu.real (frpCrossingEventFrom K y n) = mu.real B := by
    rw [frpCrossingEventFrom_eq_preimage]
    exact hpres.measureReal_preimage hBmeas.nullMeasurableSet
  rw [hstep]
  have hsub : B ⊆ frpCrossingEvent K m := by
    rintro omega ⟨_, v, _, hvout, hconn⟩
    refine ⟨Set.mem_univ _, v, Set.mem_univ _, ?_, hconn⟩
    rw [Set.mem_compl_iff]
    intro hvm
    apply hvout
    rw [Finset.mem_coe, mem_frpShiftedBox]
    exact box_shift_mem hy hvm hmLn hm
  exact measureReal_mono hsub (measure_ne_top _ _)

theorem frpCrossProb_nonneg (K : FiniteRangeKernel d) (beta : ℝ) (n : ℕ) :
    0 ≤ frpCrossProb K beta n := measureReal_nonneg

theorem frpCrossProb_le_one (K : FiniteRangeKernel d) (beta : ℝ) (n : ℕ) :
    frpCrossProb K beta n ≤ 1 := by
  unfold frpCrossProb
  rw [show (1 : ℝ) = (frpMeasure K beta).real Set.univ by rw [probReal_univ]]
  exact measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)

theorem frpCrossingEvent_antitone (K : FiniteRangeKernel d) {m n : ℕ}
    (hmn : m ≤ n) : frpCrossingEvent K n ⊆ frpCrossingEvent K m := by
  rintro omega ⟨_, z, _, hzout, hconn⟩
  refine ⟨Set.mem_univ _, z, Set.mem_univ _, ?_, hconn⟩
  rw [Set.mem_compl_iff] at hzout ⊢
  intro hzm
  exact hzout (box_mono d (by omega) hzm)

theorem frpCrossProb_antitone (K : FiniteRangeKernel d) (beta : ℝ) :
    Antitone (frpCrossProb K beta) := fun _ _ hmn =>
  measureReal_mono (frpCrossingEvent_antitone K hmn) (measure_ne_top _ _)


theorem frp_subcritical_oneStep (K : FiniteRangeKernel d) (beta : ℝ)
    (S : Finset (Site d)) (h0S : (0 : Site d) ∈ S)
    (L : ℕ) (hL : 1 ≤ L) (hRL : K.range ≤ L)
    (hSbox : (S : Set (Site d)) ⊆ box d (L - K.range))
    (k : ℕ) (hk : 1 ≤ k) :
    frpCrossProb K beta ((k + 1) * L) ≤
      frpPhi K beta S * frpCrossProb K beta (k * L) := by
  classical
  let n := (k + 1) * L
  let m := k * L
  let T : Finset (Site d) := (box_finite d (n - 1)).toFinset
  let Lam := frpOneStepClosure K T
  let B : Set (Site d) := (box d (n - 1))ᶜ
  have hm1 : 1 ≤ m := by simp only [m]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmn : m + L = n := by simp [m, n, Nat.add_mul]
  have h0T : (0 : Site d) ∈ T := by
    simp only [T, Set.Finite.mem_toFinset, mem_box]
    intro i
    simp
  have hST : (S : Set (Site d)) ⊆ (T : Set (Site d)) := by
    intro z hz
    change z ∈ (box_finite d (n - 1)).toFinset
    rw [Set.Finite.mem_toFinset]
    apply box_mono d (show L - K.range ≤ n - 1 by
      simp only [n]
      omega)
    exact hSbox hz
  have hBS : ∀ z ∈ B, z ∉ S := by
    intro z hzout hzS
    apply hzout
    change z ∈ box d (n - 1)
    rw [← show (T : Set (Site d)) = box d (n - 1) by
      ext w
      simp only [T, Finset.mem_coe, Set.Finite.mem_toFinset]]
    exact hST (by exact_mod_cast hzS)
  have hbk := frp_bk_criterion K beta Lam S (0 : Site d) B h0S hBS
  have hTcoe : (T : Set (Site d)) = box d (n - 1) := by
    ext z
    simp only [T, Finset.mem_coe, Set.Finite.mem_toFinset]
  have hleft :
      (frpMeasure K beta).real
          (connEvent (frpGraph K) (Lam : Set (Site d)) (0 : Site d) B) =
        frpCrossProb K beta n := by
    unfold Lam B frpCrossProb frpCrossingEvent
    rw [← hTcoe, ← frp_exitEvent_eq_finite K T 0 h0T]
  rw [hleft] at hbk
  calc
    frpCrossProb K beta n ≤
        ∑ q ∈ frpBoundaryPairs K S,
          (frpEdgeParam K beta s(q.1, q.2) : ℝ) *
            (frpMeasure K beta).real
              (connEvent (frpGraph K) (S : Set (Site d)) 0 {q.1}) *
            frpCrossProb K beta m := by
      refine hbk.trans (Finset.sum_le_sum fun q hq => ?_)
      have hqm := (mem_frpBoundaryPairs K S).mp hq
      have hxbox : q.1 ∈ box d (L - K.range) := hSbox (by exact_mod_cast hqm.1)
      have hybox0 : q.2 ∈ box d ((L - K.range) + K.range) :=
        frp_adj_mem_box_add K hxbox hqm.2.2
      have hybox : q.2 ∈ box d L := by
        rwa [Nat.sub_add_cancel hRL] at hybox0
      have htailSub :
          connEvent (frpGraph K) (Lam : Set (Site d)) q.2 B ⊆
            frpCrossingEventFrom K q.2 n := by
        rintro omega ⟨hy, z, hz, hzB, hconn⟩
        exact ⟨Set.mem_univ _, z, Set.mem_univ _, hzB,
          frp_connWithin_mono_set K omega (Set.subset_univ _) hconn⟩
      have htail :
          (frpMeasure K beta).real
              (connEvent (frpGraph K) (Lam : Set (Site d)) q.2 B) ≤
            frpCrossProb K beta m :=
        (measureReal_mono htailSub (measure_ne_top _ _)).trans
          (frp_crossProbFrom_le K beta q.2 hybox hmn.le hm1)
      have hcoef : 0 ≤
          (frpEdgeParam K beta s(q.1, q.2) : ℝ) *
            (frpMeasure K beta).real
              (connEvent (frpGraph K) (S : Set (Site d)) 0 {q.1}) :=
        mul_nonneg (frpEdgeParam K beta s(q.1, q.2)).coe_nonneg measureReal_nonneg
      exact mul_le_mul_of_nonneg_left htail hcoef
    _ = frpPhi K beta S * frpCrossProb K beta m := by
      unfold frpPhi
      rw [Finset.sum_mul]

theorem frpPhi_nonneg (K : FiniteRangeKernel d) (beta : ℝ)
    (S : Finset (Site d)) : 0 ≤ frpPhi K beta S := by
  unfold frpPhi
  apply Finset.sum_nonneg
  intro q _
  exact mul_nonneg (frpEdgeParam K beta s(q.1, q.2)).coe_nonneg
    measureReal_nonneg


theorem frp_subcritical_geometric (K : FiniteRangeKernel d) (beta : ℝ)
    (S : Finset (Site d)) (h0S : (0 : Site d) ∈ S)
    (hphi : frpPhi K beta S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hRL : K.range ≤ L)
    (hSbox : (S : Set (Site d)) ⊆ box d (L - K.range)) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ k,
      frpCrossProb K beta (k * L) ≤ r⁻¹ * r ^ k := by
  let g : ℕ → ℝ := fun k => frpCrossProb K beta ((k + 1) * L)
  have hgnn : ∀ k, 0 ≤ g k := fun k => frpCrossProb_nonneg K beta _
  have hg0 : g 0 ≤ 1 := by
    simpa [g] using frpCrossProb_le_one K beta ((0 + 1) * L)
  have hgrec : ∀ k, g (k + 1) ≤ frpPhi K beta S * g k := by
    intro k
    have hstep := frp_subcritical_oneStep K beta S h0S L hL hRL hSbox
      (k + 1) (by omega)
    simp only [g]
    convert hstep using 2
  obtain ⟨r, hr0, hr1, hgrec'⟩ := step_with_pos_ratio hgnn hphi hgrec
  have hsubg : ∀ k, g k ≤ r ^ k := recursion_le_pow hg0 hr0.le hgrec'
  refine ⟨r, hr0, hr1, fun k => ?_⟩
  cases k with
  | zero =>
      simp only [Nat.zero_mul, pow_zero, mul_one]
      have h1 : frpCrossProb K beta 0 ≤ 1 := frpCrossProb_le_one K beta 0
      have h2 : (1 : ℝ) ≤ r⁻¹ := by
        rw [one_le_inv_iff₀]
        exact ⟨hr0, hr1.le⟩
      linarith
  | succ j =>
      have hj : frpCrossProb K beta ((j + 1) * L) ≤ r ^ j := hsubg j
      rw [show r⁻¹ * r ^ (j + 1) = r ^ j from by field_simp; ring]
      exact hj


theorem frp_subcritical_decay (K : FiniteRangeKernel d) (beta : ℝ)
    (S : Finset (Site d)) (h0S : (0 : Site d) ∈ S)
    (hphi : frpPhi K beta S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hRL : K.range ≤ L)
    (hSbox : (S : Set (Site d)) ⊆ box d (L - K.range)) :
    ∃ c > 0, ∃ C > 0, ∀ n,
      frpCrossProb K beta n ≤ C * Real.exp (-c * n) := by
  obtain ⟨r, hr0, hr1, hsub⟩ :=
    frp_subcritical_geometric K beta S h0S hphi L hL hRL hSbox
  exact geometric_subseq_antitone_decay' hL hr0 hr1 (by positivity)
    (frpCrossProb_antitone K beta) hsub

theorem frpEdgeParam_eq_zero_of_nonpos (K : FiniteRangeKernel d)
    {beta : ℝ} (hbeta : beta ≤ 0) (e : Sym2 (Site d)) :
    frpEdgeParam K beta e = 0 := by
  unfold frpEdgeParam
  rw [Real.toNNReal_eq_zero]
  have hJ := K.nonneg
  have hexp : 1 ≤ Real.exp (-beta * frpEdgeCoupling K e) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg (neg_nonneg.mpr hbeta)
      (by
        induction e using Sym2.inductionOn with
        | _ x y => exact K.nonneg (y - x)))
  linarith

theorem frpPhi_eq_zero_of_nonpos (K : FiniteRangeKernel d)
    {beta : ℝ} (hbeta : beta ≤ 0) (S : Finset (Site d)) :
    frpPhi K beta S = 0 := by
  unfold frpPhi
  apply Finset.sum_eq_zero
  intro q _
  rw [frpEdgeParam_eq_zero_of_nonpos K hbeta]
  simp


end Sharpness
end StatMech
