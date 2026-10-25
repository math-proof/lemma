/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part11
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem hasFDerivAt_sixVertexBethePotential
    {c : ℝ} (hc : 2 < c) (N n : ℕ) (p : Fin n → ℝ) :
    HasFDerivAt (sixVertexBethePotential hc N n)
      (sixVertexBetheOneForm hc N n p) p := by
  unfold sixVertexBethePotential sixVertexBetheOneForm
  apply HasFDerivAt.add
  · apply HasFDerivAt.fun_sum
    intro j _
    have hj := hasFDerivAt_apply (𝕜 := ℝ) j p
    have h := (hasDerivAt_sixVertexBetheOneBodyPotential hc N
      (sixVertexCentralQuantumNumber j) (p j)).comp_hasFDerivAt p hj
    simpa using h
  · apply HasFDerivAt.fun_sum
    intro j _
    apply HasFDerivAt.fun_sum
    intro k hk
    have hj := hasFDerivAt_apply (𝕜 := ℝ) j p
    have hk' := hasFDerivAt_apply (𝕜 := ℝ) k p
    exact (hasFDerivAt_sixVertexBethePairPotential hc (p j, p k)).comp p
      (hj.prodMk hk')

theorem sum_Iio_swap {n : ℕ} (F : Fin n → Fin n → ℝ) :
    (∑ j, ∑ k ∈ Finset.Iio j, F j k) =
      ∑ j, ∑ k ∈ Finset.Ioi j, F k j := by
  classical
  have hIio (j : Fin n) : Finset.Iio j =
      Finset.univ.filter fun k => k < j := by
    ext k
    simp
  have hIoi (j : Fin n) : Finset.Ioi j =
      Finset.univ.filter fun k => j < k := by
    ext k
    simp
  calc
    (∑ j, ∑ k ∈ Finset.Iio j, F j k) =
        ∑ j, ∑ k, if k < j then F j k else 0 := by
      simp_rw [hIio, Finset.sum_filter]
    _ = ∑ k, ∑ j, if k < j then F j k else 0 := Finset.sum_comm
    _ = ∑ k, ∑ j ∈ Finset.Ioi k, F j k := by
      simp_rw [hIoi, Finset.sum_filter]

theorem sum_unorderedPair_expand {n : ℕ}
    (H : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    (∑ j, ∑ k ∈ Finset.Ioi j,
      (H j k * v j + H k j * v k)) =
      ∑ j, (∑ k ∈ Finset.univ.erase j, H j k) * v j := by
  classical
  have herase (j : Fin n) : Finset.univ.erase j =
      Finset.Iio j ∪ Finset.Ioi j := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi]
    omega
  have hdisj (j : Fin n) : Disjoint (Finset.Iio j) (Finset.Ioi j) := by
    rw [Finset.disjoint_left]
    intro k hkj hjk
    simp only [Finset.mem_Iio] at hkj
    simp only [Finset.mem_Ioi] at hjk
    omega
  simp_rw [Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul]
  have hswap := sum_Iio_swap (fun j k => H j k * v j)
  calc
    (∑ x, (∑ j ∈ Finset.Ioi x, H x j) * v x) +
          ∑ x, ∑ j ∈ Finset.Ioi x, H j x * v j =
        (∑ x, (∑ j ∈ Finset.Ioi x, H x j) * v x) +
          ∑ x, ∑ j ∈ Finset.Iio x, H x j * v x := by rw [hswap]
    _ = ∑ j, ((∑ k ∈ Finset.Iio j, H j k) +
          ∑ k ∈ Finset.Ioi j, H j k) * v j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [herase, Finset.sum_union (hdisj j)]

theorem sum_clm_apply {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ι → E →L[ℝ] ℝ) (v : E) :
    (∑ i, f i) v = ∑ i, f i v := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

theorem sum_clm_apply_finset {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (f : ι → E →L[ℝ] ℝ) (v : E) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

theorem sixVertexBetheOneForm_apply
    {c : ℝ} (hc : 2 < c) (N n : ℕ)
    (p v : Fin n → ℝ) :
    sixVertexBetheOneForm hc N n p v =
      ∑ j, sixVertexNormalizedBetheResidual c N n p j * v j := by
  classical
  let H : Fin n → Fin n → ℝ := fun j k =>
    sixVertexNormalizedTheta c (p j) (p k)
  have hpair := sum_unorderedPair_expand H v
  unfold sixVertexBetheOneForm
  rw [ContinuousLinearMap.add_apply,
    sum_clm_apply (fun j =>
      sixVertexBetheOneBodyCoefficient c N
        (sixVertexCentralQuantumNumber j) (p j) •
          ContinuousLinearMap.proj j) v,
    sum_clm_apply (fun j => ∑ k ∈ Finset.Ioi j,
      (sixVertexBethePairOneForm c (p j, p k)).comp
        ((ContinuousLinearMap.proj j).prod
          (ContinuousLinearMap.proj k))) v]
  simp_rw [sum_clm_apply_finset]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.proj_apply,
    sixVertexBethePairOneForm, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply]
  simp only [smul_eq_mul]
  simp
  have hpair' :
      (∑ j, ∑ k ∈ Finset.Ioi j, (v j * H j k + v k * H k j)) =
        ∑ j, (∑ k ∈ Finset.univ.erase j, H j k) * v j := by
    simpa [mul_comm] using hpair
  rw [hpair', ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hself : H j j = 0 := by
    simp [H, sixVertexNormalizedTheta]
  have hsum : (∑ k, H j k) = ∑ k ∈ Finset.univ.erase j, H j k := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), hself, add_zero]
  rw [← hsum]
  simp only [H]
  unfold sixVertexNormalizedBetheResidual sixVertexBetheResidual
    sixVertexBetheOneBodyCoefficient sixVertexNormalizedTheta
  rw [← Finset.sum_div]
  ring

theorem sixVertexBetheResidual_eq_updateSub
    {c : ℝ} {N n : ℕ} (hN : 0 < N) (p : Fin n → ℝ) (j : Fin n) :
    sixVertexBetheResidual c N n p j =
      (N : ℝ) * (p j - sixVertexBetheUpdate c N n p j) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold sixVertexBetheResidual sixVertexBetheUpdate
  field_simp [hN0]
  ring

theorem sixVertexBetheOneForm_updateSub
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (hN : 0 < N)
    (p : Fin n → ℝ) :
    sixVertexBetheOneForm hc N n p
        (sixVertexBetheUpdate c N n p - p) =
      -(N : ℝ) * ∑ j,
        (sixVertexBetheUpdate c N n p j - p j) ^ 2 /
          sixVertexBetheIntegratingFactor c (p j) := by
  rw [sixVertexBetheOneForm_apply]
  calc
    (∑ j, sixVertexNormalizedBetheResidual c N n p j *
        (sixVertexBetheUpdate c N n p - p) j) =
        ∑ j, -(N : ℝ) *
          ((sixVertexBetheUpdate c N n p j - p j) ^ 2 /
            sixVertexBetheIntegratingFactor c (p j)) := by
      apply Finset.sum_congr rfl
      intro j _
      change sixVertexNormalizedBetheResidual c N n p j *
        (sixVertexBetheUpdate c N n p j - p j) = _
      unfold sixVertexNormalizedBetheResidual
      rw [sixVertexBetheResidual_eq_updateSub hN]
      ring
    _ = _ := by rw [Finset.mul_sum]

theorem sixVertexBetheOneForm_updateSub_neg
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (hN : 0 < N)
    (p : Fin n → ℝ)
    (hne : sixVertexBetheUpdate c N n p ≠ p) :
    sixVertexBetheOneForm hc N n p
        (sixVertexBetheUpdate c N n p - p) < 0 := by
  have hex : ∃ j, sixVertexBetheUpdate c N n p j - p j ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    funext j
    linarith [h j]
  have hnonneg (j : Fin n) :
      0 ≤ (sixVertexBetheUpdate c N n p j - p j) ^ 2 /
        sixVertexBetheIntegratingFactor c (p j) :=
    div_nonneg (sq_nonneg _) (sixVertexBetheIntegratingFactor_pos hc _).le
  have hsum : 0 < ∑ j,
      (sixVertexBetheUpdate c N n p j - p j) ^ 2 /
        sixVertexBetheIntegratingFactor c (p j) := by
    apply Finset.sum_pos'
    · intro j _
      exact hnonneg j
    · obtain ⟨j, hj⟩ := hex
      refine ⟨j, Finset.mem_univ j, ?_⟩
      exact div_pos (sq_pos_of_ne_zero hj)
        (sixVertexBetheIntegratingFactor_pos hc _)
  rw [sixVertexBetheOneForm_updateSub hc hN]
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith

theorem continuous_sixVertexBethePotential
    {c : ℝ} (hc : 2 < c) (N n : ℕ) :
    Continuous (sixVertexBethePotential hc N n) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact (hasFDerivAt_sixVertexBethePotential hc N n p).continuousAt


theorem exists_sixVertexBetheUpdate_fixedPoint
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (hN : 0 < N)
    (hhalf : 2 * n ≤ N) :
    ∃ p : Fin n → ℝ, SixVertexClosedRootSimplex p ∧
      sixVertexBetheUpdate c N n p = p := by
  let S : Set (Fin n → ℝ) :=
    {p | SixVertexClosedRootSimplex p}
  obtain ⟨p, hp, hmin⟩ :=
    (isCompact_sixVertexClosedRootSimplex n).exists_isMinOn
      (sixVertexClosedRootSimplex_nonempty n)
      (continuous_sixVertexBethePotential hc N n).continuousOn
  refine ⟨p, hp, ?_⟩
  by_contra hne
  let q := sixVertexBetheUpdate c N n p
  have hq : q ∈ S := by
    exact sixVertexBetheUpdate_mapsTo_closedRootSimplex hc hhalf hp
  have hdir : q - p ∈ posTangentConeAt S p :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_sixVertexClosedRootSimplex n).segment_subset hp hq)
  have hnonneg :
      0 ≤ sixVertexBetheOneForm hc N n p (q - p) :=
    hmin.localize.hasFDerivWithinAt_nonneg
      (hasFDerivAt_sixVertexBethePotential hc N n p).hasFDerivWithinAt
      hdir
  have hneg : sixVertexBetheOneForm hc N n p (q - p) < 0 := by
    simpa only [q] using sixVertexBetheOneForm_updateSub_neg hc hN p hne
  exact (not_lt_of_ge hnonneg) hneg


theorem exists_sixVertexBetheSolution
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (hhalf : 2 * n ≤ N) :
    ∃ p : Fin n → ℝ, SixVertexOpenRootSimplex p ∧
      SixVertexSatisfiesBetheEquations c N n p := by
  by_cases hNzero : N = 0
  · subst N
    have hnzero : n = 0 := by omega
    subst n
    refine ⟨fun j => Fin.elim0 j, ?_, ?_⟩
    · exact ⟨fun i => Fin.elim0 i,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    · exact fun i => Fin.elim0 i
  · have hN : 0 < N := Nat.pos_of_ne_zero hNzero
    obtain ⟨p, hp, hfix⟩ :=
      exists_sixVertexBetheUpdate_fixedPoint hc hN hhalf
    exact ⟨p,
      sixVertexBetheUpdate_fixedPoint_mem_open hc hhalf hp hfix,
      sixVertexBetheUpdate_fixedPoint_is_solution hN hfix⟩


end
end StatMech.FrontierD
