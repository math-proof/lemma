/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumErgodicFactor.Part2
import Theorem.StatisticalMechanics.Code.FK.FreePairMixingFromTail.Part3
import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Def.StatisticalMechanics.Code.FK.PottsClusterSumProductErgodicity
open Filter Function MeasureTheory MeasurableSpace Set Topology
open scoped ENNReal symmDiff


namespace StatMech.FK

theorem section_preimage_prodMap_iterate
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    (T : Alpha -> Alpha) (S : Beta -> Beta)
    {A : Set (Alpha × Beta)}
    (hA : (Prod.map T S) ⁻¹' A = A) (n : Nat) (x : Alpha) :
    (S^[n]) ⁻¹' (Prod.mk (T^[n] x) ⁻¹' A) = Prod.mk x ⁻¹' A := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      ext y
      simp only [Set.mem_preimage, iterate_succ_apply]
      rw [show (T^[n] (T x), S^[n] (S y)) ∈ A ↔ (T x, S y) ∈ A from
        Set.ext_iff.mp (ih (T x)) (S y)]
      exact Set.ext_iff.mp hA (x, y)

theorem measurable_sectionReal
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    {nu : Measure Beta} [IsFiniteMeasure nu]
    {A : Set (Alpha × Beta)} (hA : MeasurableSet A) :
    Measurable fun x => nu.real (Prod.mk x ⁻¹' A) := by
  exact ENNReal.measurable_toReal.comp
    (measurable_measure_prodMk_left hA)

theorem sectionReal_comp_iterate
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    {nu : Measure Beta} [IsFiniteMeasure nu]
    (T : Alpha -> Alpha) (S : Beta -> Beta)
    (hS : MeasurePreserving S nu nu)
    {A : Set (Alpha × Beta)}
    (hA : MeasurableSet A) (hinv : (Prod.map T S) ⁻¹' A = A)
    (B : Set Beta) (hB : MeasurableSet B) (n : Nat) (x : Alpha) :
    nu.real ((Prod.mk (T^[n] x) ⁻¹' A) ∩ B) =
      nu.real ((Prod.mk x ⁻¹' A) ∩ (S^[n]) ⁻¹' B) := by
  let Axn := Prod.mk (T^[n] x) ⁻¹' A
  have hAxn : MeasurableSet Axn := measurable_prodMk_left hA
  have hmp := hS.iterate n
  calc
    nu.real (Axn ∩ B) =
        nu.real ((S^[n]) ⁻¹' (Axn ∩ B)) :=
      (hmp.measureReal_preimage (hAxn.inter hB).nullMeasurableSet).symm
    _ = nu.real ((Prod.mk x ⁻¹' A) ∩ (S^[n]) ⁻¹' B) := by
      congr 1
      rw [preimage_inter, section_preimage_prodMap_iterate T S hinv]

set_option maxHeartbeats 2000000 in


theorem ergodic_prod_of_mixingAgainst
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    {mu : Measure Alpha} {nu : Measure Beta}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (T : Alpha -> Alpha) (S : Beta -> Beta)
    (hT : _root_.Ergodic T mu) (hS : MeasurePreserving S nu nu)
    (D : Set (Set Beta))
    (hDgen : generateFrom D = (inferInstance : MeasurableSpace Beta))
    (hDpi : IsPiSystem D) (hDspan : IsCountablySpanning D)
    (hDmeas : forall B, B ∈ D -> MeasurableSet B)
    (hmix : MixingAgainst S nu D) :
    _root_.Ergodic (Prod.map T S) (mu.prod nu) := by
  classical
  refine ⟨hT.toMeasurePreserving.prod hS, ⟨?_⟩⟩
  intro A hA hinv
  let r : Alpha -> Real := fun x => nu.real (Prod.mk x ⁻¹' A)
  have hrmeas : Measurable r := measurable_sectionReal hA
  have hrinv : r ∘ T = r := by
    funext x
    have hpre := section_preimage_prodMap_iterate T S hinv 1 x
    simp only [iterate_one] at hpre
    calc
      r (T x) = nu.real (Prod.mk (T x) ⁻¹' A) := rfl
      _ = nu.real (S ⁻¹' (Prod.mk (T x) ⁻¹' A)) :=
        (hS.measureReal_preimage
          (measurable_prodMk_left hA).nullMeasurableSet).symm
      _ = r x := congrArg nu.real hpre
  obtain ⟨c, hc⟩ := hT.toPreErgodic.ae_eq_const_of_ae_eq_comp
    hrmeas hrinv
  have hc_nonneg : 0 <= c := by
    obtain ⟨x, hx⟩ := hc.exists
    simpa only [r, const_apply, hx] using
      (measureReal_nonneg (μ := nu) (s := Prod.mk x ⁻¹' A))
  have hc_le_one : c <= 1 := by
    obtain ⟨x, hx⟩ := hc.exists
    simpa only [r, const_apply, hx] using
      (measureReal_le_one (μ := nu) (s := Prod.mk x ⁻¹' A))

  have hsection (B : Set Beta) (hBD : B ∈ D) :
      (fun x => nu.real ((Prod.mk x ⁻¹' A) ∩ B)) =ᵐ[mu]
        (fun _ => c * nu.real B) := by
    have hB := hDmeas B hBD
    let phi : Alpha -> Real := fun x =>
      nu.real ((Prod.mk x ⁻¹' A) ∩ B)
    have hphimeas : Measurable phi := by
      have hset : MeasurableSet (A ∩ (Set.univ ×ˢ B)) :=
        hA.inter (MeasurableSet.univ.prod hB)
      have hm := measurable_sectionReal (nu := nu) hset
      convert hm using 1
      funext x
      apply congrArg nu.real
      ext y
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod,
        Set.mem_univ, true_and]
    have hpoint : forall x, Tendsto (fun n : Nat => phi (T^[n] x)) atTop
        (nhds (r x * nu.real B)) := by
      intro x
      have hxmeas : MeasurableSet (Prod.mk x ⁻¹' A) :=
        measurable_prodMk_left hA
      simpa only [phi, r,
        sectionReal_comp_iterate T S hS hA hinv B hB] using
        hmix (Prod.mk x ⁻¹' A) hxmeas B hBD
    have hpointc : ∀ᵐ x ∂mu,
        Tendsto (fun n : Nat => phi (T^[n] x)) atTop
          (nhds (c * nu.real B)) := by
      filter_upwards [hc] with x hx
      simpa only [r, const_apply, hx] using hpoint x
    have hnormlim : Tendsto (fun n : Nat =>
        ∫ x, |phi (T^[n] x) - c * nu.real B| ∂mu)
        atTop (nhds 0) := by
      have hdct := tendsto_integral_of_dominated_convergence
        (μ := mu) (F := fun n x =>
          |phi (T^[n] x) - c * nu.real B|)
        (f := fun _ => (0 : Real)) (fun _ => (1 : Real))
        (fun n => ((hphimeas.comp (hT.measurable.iterate n)).sub
          measurable_const).abs.aestronglyMeasurable)
        (integrable_const 1)
        (by
          intro n
          filter_upwards with x
          rw [Real.norm_eq_abs, abs_abs]
          have hphi0 : 0 <= phi (T^[n] x) := measureReal_nonneg
          have hphi1 : phi (T^[n] x) <= 1 := measureReal_le_one
          have hB0 : 0 <= nu.real B := measureReal_nonneg
          have hB1 : nu.real B <= 1 := measureReal_le_one
          have hprod0 : 0 <= c * nu.real B := mul_nonneg hc_nonneg hB0
          have hprod1 : c * nu.real B <= 1 :=
            mul_le_one₀ hc_le_one hB0 hB1
          exact abs_le.mpr ⟨by linarith, by linarith⟩)
        (by
          filter_upwards [hpointc] with x hx
          have hconst : Tendsto (fun _ : Nat => c * nu.real B) atTop
              (nhds (c * nu.real B)) := tendsto_const_nhds
          simpa only [sub_self, abs_zero] using (hx.sub hconst).abs)
      simpa using hdct
    have hintegral_eq (n : Nat) :
        (∫ x, |phi (T^[n] x) - c * nu.real B| ∂mu) =
          ∫ x, |phi x - c * nu.real B| ∂mu := by
      let f : Alpha -> Real := fun x => |phi x - c * nu.real B|
      have hfmeas : Measurable f :=
        (hphimeas.sub measurable_const).abs
      have hfint : Integrable f mu := by
        apply Integrable.mono' (integrable_const 1) hfmeas.aestronglyMeasurable
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_abs]
        have hphi0 : 0 <= phi x := measureReal_nonneg
        have hphi1 : phi x <= 1 := measureReal_le_one
        have hB0 : 0 <= nu.real B := measureReal_nonneg
        have hB1 : nu.real B <= 1 := measureReal_le_one
        have hprod0 : 0 <= c * nu.real B := mul_nonneg hc_nonneg hB0
        have hprod1 : c * nu.real B <= 1 :=
          mul_le_one₀ hc_le_one hB0 hB1
        simpa only [f, Real.norm_eq_abs, abs_abs] using
          (abs_le.mpr ⟨by linarith, by linarith⟩)
      have hmp := hT.toMeasurePreserving.iterate n
      calc
        (∫ x, |phi (T^[n] x) - c * nu.real B| ∂mu) =
            ∫ x, f (T^[n] x) ∂mu := rfl
        _ = ∫ x, f x ∂mu := by
          calc
            (∫ x, f (T^[n] x) ∂mu) =
                ∫ x, f x ∂Measure.map (T^[n]) mu :=
              (integral_map (hT.measurable.iterate n).aemeasurable
                (by rw [hmp.map_eq]; exact hfmeas.aestronglyMeasurable)).symm
            _ = ∫ x, f x ∂mu := by rw [hmp.map_eq]
        _ = ∫ x, |phi x - c * nu.real B| ∂mu := rfl
    have hzero : (∫ x, |phi x - c * nu.real B| ∂mu) = 0 := by
      have ht : Tendsto (fun _ : Nat =>
          ∫ x, |phi x - c * nu.real B| ∂mu) atTop (nhds 0) := by
        simpa only [hintegral_eq] using hnormlim
      exact tendsto_nhds_unique tendsto_const_nhds ht
    have hae_zero : (fun x => |phi x - c * nu.real B|) =ᵐ[mu] 0 := by
      have hint : Integrable (fun x => |phi x - c * nu.real B|) mu := by
        apply Integrable.mono' (integrable_const 1)
          (hphimeas.sub measurable_const).abs.aestronglyMeasurable
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_abs]
        have hphi0 : 0 <= phi x := measureReal_nonneg
        have hphi1 : phi x <= 1 := measureReal_le_one
        have hB0 : 0 <= nu.real B := measureReal_nonneg
        have hB1 : nu.real B <= 1 := measureReal_le_one
        have hprod0 : 0 <= c * nu.real B := mul_nonneg hc_nonneg hB0
        have hprod1 : c * nu.real B <= 1 :=
          mul_le_one₀ hc_le_one hB0 hB1
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      exact (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) hint).mp hzero
    filter_upwards [hae_zero] with x hx
    exact sub_eq_zero.mp (abs_eq_zero.mp hx)

  let lambda : Measure (Alpha × Beta) := (mu.prod nu).restrict A
  let cE : ENNReal := ENNReal.ofReal c
  have hmassE : (mu.prod nu) A = cE := by
    rw [Measure.prod_apply hA]
    have hsecE :
        (fun x => nu (Prod.mk x ⁻¹' A)) =ᵐ[mu] (fun _ => cE) := by
      filter_upwards [hc] with x hx
      apply (ENNReal.toReal_eq_toReal_iff'
        (measure_ne_top nu _) ENNReal.ofReal_ne_top).mp
      simpa only [Measure.real, cE, ENNReal.toReal_ofReal hc_nonneg] using hx
    rw [lintegral_congr_ae hsecE, lintegral_const, measure_univ, mul_one]
  have hlambda : lambda = cE • (mu.prod nu) := by
    let C : Set (Set (Alpha × Beta)) :=
      Set.image2 (fun U V => U ×ˢ V)
        {U : Set Alpha | MeasurableSet U} D
    have hAlphaSpan : IsCountablySpanning
        {U : Set Alpha | MeasurableSet U} :=
      isCountablySpanning_measurableSet
    have hgen : (inferInstance : MeasurableSpace (Alpha × Beta)) =
        generateFrom C := by
      symm
      exact generateFrom_eq_prod generateFrom_measurableSet hDgen
        hAlphaSpan hDspan
    have hpi : IsPiSystem C := isPiSystem_measurableSet.prod hDpi
    apply ext_of_generate_finite C hgen hpi
    · intro R hR
      obtain ⟨U, hU, B, hBD, rfl⟩ := hR
      have hB := hDmeas B hBD
      have hrect : MeasurableSet (U ×ˢ B) := hU.prod hB
      dsimp only [lambda]
      rw [Measure.smul_apply, Measure.restrict_apply hrect,
        Set.inter_comm (U ×ˢ B) A,
        Measure.prod_apply (hA.inter hrect), Measure.prod_prod]
      have hsecE :
          (fun x => nu (Prod.mk x ⁻¹' (A ∩ (U ×ˢ B)))) =ᵐ[mu]
            (fun x => if x ∈ U then cE * nu B else 0) := by
        filter_upwards [hsection B hBD] with x hx
        have hrectsec : Prod.mk x ⁻¹' (U ×ˢ B) =
            if x ∈ U then B else ∅ := by
          ext y
          simp
        rw [Set.preimage_inter, hrectsec]
        by_cases hxU : x ∈ U
        · simp only [hxU, if_true]
          apply (ENNReal.toReal_eq_toReal_iff'
            (measure_ne_top nu _) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              (measure_ne_top nu B))).mp
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc_nonneg,
            ← Measure.real, ← Measure.real]
          exact hx
        · simp only [hxU, if_false, Set.inter_empty, measure_empty]
      rw [lintegral_congr_ae hsecE]
      have hfun : (fun x : Alpha => if x ∈ U then cE * nu B else 0) =
          U.indicator (fun _ => cE * nu B) := by
        funext x
        by_cases hx : x ∈ U <;> simp [Set.indicator, hx]
      rw [hfun, lintegral_indicator hU, lintegral_const]
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp only [Set.univ_inter, smul_eq_mul]
      ac_rfl
    · simp [lambda, cE, hmassE]

  have hmass : (mu.prod nu).real A = c := by
    rw [Measure.real, hmassE]
    dsimp only [cE]
    rw [ENNReal.toReal_ofReal hc_nonneg]
  have hidem : c = c * c := by
    have h := congrArg (fun m : Measure (Alpha × Beta) => m A) hlambda
    simp only [lambda, Measure.restrict_apply hA, Set.inter_self,
      Measure.smul_apply, cE] at h
    apply_fun ENNReal.toReal at h
    simp only [smul_eq_mul] at h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc_nonneg,
      ← Measure.real, hmass] at h
    exact h
  have hc01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by nlinarith [hidem]
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rw [eventuallyConst_set']
  rcases hc01 with rfl | rfl
  · left
    apply ae_eq_empty.mpr
    apply (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top (mu.prod nu) A) (by simp)).mp
    simpa [Measure.real] using hmass
  · right
    apply ae_eq_univ.mpr
    have hone : (mu.prod nu) A = 1 := by
      apply (ENNReal.toReal_eq_toReal_iff'
        (measure_ne_top (mu.prod nu) A) (by simp)).mp
      simpa [Measure.real] using hmass
    rw [measure_compl hA (measure_ne_top (mu.prod nu) A), hone]
    simp


open Lattice

theorem pottsLabelShift_eq_piCongrLeft {d q : Nat}
    (g : Multiplicative (Site d)) :
    (pottsLabelShift g : (Site d -> Fin q) -> (Site d -> Fin q)) =
      ⇑(Equiv.piCongrLeft (fun _ : Site d => Fin q)
        (MulAction.toPerm g)) := by
  funext label x
  set e := MulAction.toPerm (β := Site d) g with he
  conv_rhs => rw [show x = e (e.symm x) from (e.apply_symm_apply x).symm,
    Equiv.piCongrLeft_apply_apply (a := e.symm x)]
  rw [pottsLabelShift, he, MulAction.toPerm_symm_apply]


theorem pottsIIDLabelMeasure_measurePreserving {d q : Nat} [NeZero q]
    (g : Multiplicative (Site d)) :
    MeasurePreserving (pottsLabelShift g)
      (pottsIIDLabelMeasure d q) (pottsIIDLabelMeasure d q) := by
  have hmeas : Measurable (pottsLabelShift g :
      (Site d -> Fin q) -> (Site d -> Fin q)) := by
    rw [pottsLabelShift_eq_piCongrLeft]
    exact (MeasurableEquiv.piCongrLeft (fun _ : Site d => Fin q)
      (MulAction.toPerm g)).measurable
  refine ⟨hmeas, ?_⟩
  rw [pottsLabelShift_eq_piCongrLeft]
  have h := Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : Site d => (PMF.uniformOfFintype (Fin q)).toMeasure)
    (MulAction.toPerm (β := Site d) g)
  simpa only [pottsIIDLabelMeasure] using h

theorem pottsLabelShift_mul {d q : Nat}
    (g h : Multiplicative (Site d)) :
    (pottsLabelShift (g * h) : (Site d -> Fin q) -> (Site d -> Fin q)) =
      pottsLabelShift g ∘ pottsLabelShift h := by
  funext label x
  simp [pottsLabelShift, mul_smul]

theorem pottsLabelShift_freeAxisTranslationPower {d q : Nat}
    (hd : 1 <= d) (n : Nat) :
    (pottsLabelShift (freeAxisTranslationPower hd n) :
      (Site d -> Fin q) -> (Site d -> Fin q)) =
      (pottsLabelShift (freeAxisTranslation hd))^[n] := by
  rw [freeAxisTranslationPower_eq_pow]
  induction n with
  | zero =>
      funext label x
      simp [pottsLabelShift]
  | succ n ih =>
      rw [pow_succ, pottsLabelShift_mul, ih, Function.iterate_succ]

theorem pottsLabelShift_preimage_cylinder {d q : Nat}
    (g : Multiplicative (Site d)) (t : Finset (Site d))
    (T : Set (t -> Fin q)) :
    (pottsLabelShift g : (Site d -> Fin q) -> (Site d -> Fin q)) ⁻¹'
        cylinder t T =
      cylinder (t.image (fun x => g⁻¹ • x))
        ((fun (label : (t.image (fun x => g⁻¹ • x)) -> Fin q) (x : t) =>
          label ⟨g⁻¹ • (x : Site d), Finset.mem_image_of_mem _ x.2⟩) ⁻¹' T) := by
  ext label
  simp only [cylinder, Set.mem_preimage]
  rfl

end StatMech.FK
