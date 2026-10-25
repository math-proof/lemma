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
import Def.StatisticalMechanics.Code.FK.PottsClusterSumProductErgodicity.Part2
open Filter Function MeasureTheory MeasurableSpace Set Topology
open scoped ENNReal symmDiff


namespace StatMech.FK

open Lattice

theorem pottsInverseAxisFinset_eventually_outside_box {d : Nat}
    (hd : 1 <= d) (B : Finset (Site d)) (m : Nat) :
    ∀ᶠ n in atTop, (pottsInverseAxisFinset hd n B : Set (Site d)) ⊆
      (box d m)ᶜ := by
  let M := B.sup fun x => (x ⟨0, hd⟩).natAbs
  filter_upwards [eventually_ge_atTop (M + m + 1)] with n hn
  intro z hz
  simp only [pottsInverseAxisFinset, Finset.coe_image, Set.mem_image,
    Finset.mem_coe] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [Set.mem_compl_iff]
  intro hbox
  have hxBound : x ⟨0, hd⟩ <= (M : Int) := by
    exact (Int.le_natAbs.trans (by exact_mod_cast
      (Finset.le_sup (f := fun x => (x ⟨0, hd⟩).natAbs) hx)))
  have hcoord := hbox ⟨0, hd⟩
  have hval :
      (((freeAxisTranslationPower hd n)⁻¹ • x) ⟨0, hd⟩) =
        x ⟨0, hd⟩ - n := by
    change (-(Multiplicative.toAdd (freeAxisTranslationPower hd n)) + x)
      ⟨0, hd⟩ = _
    simp [freeAxisTranslationPower]
    ring
  rw [hval] at hcoord
  have hneg : x ⟨0, hd⟩ - (n : Int) <= -(m + 1 : Int) := by omega
  have habs : ((x ⟨0, hd⟩ - (n : Int)).natAbs : Int) =
      -(x ⟨0, hd⟩ - (n : Int)) := by
    rw [← Int.natAbs_neg, Int.natAbs_of_nonneg]
    omega
  have hcoord' : ((x ⟨0, hd⟩ - (n : Int)).natAbs : Int) <= m := by
    exact_mod_cast hcoord
  rw [habs] at hcoord'
  omega

theorem pottsAxisFinsets_eventually_disjoint {d : Nat}
    (hd : 1 <= d) (s t : Finset (Site d)) :
    ∀ᶠ n in atTop, Disjoint s
      (t.image (fun x => (freeAxisTranslationPower hd n)⁻¹ • x)) := by
  obtain ⟨m, hm⟩ := Percolation.finite_subset_box
    (s : Set (Site d)) s.finite_toSet
  filter_upwards [pottsInverseAxisFinset_eventually_outside_box hd t m]
    with n hn
  rw [Finset.disjoint_left]
  intro x hxs hxt
  have hxbox : x ∈ box d m := hm hxs
  have hxout : x ∈ (box d m)ᶜ := hn hxt
  exact hxout hxbox

theorem pottsIIDLabel_cylinders_axis_factor {d q : Nat} [NeZero q]
    (hd : 1 <= d) (s t : Finset (Site d))
    (S : Set (s -> Fin q)) (T : Set (t -> Fin q))
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∀ᶠ n in atTop,
      (pottsIIDLabelMeasure d q).real
          (cylinder s S ∩
            ((pottsLabelShift (freeAxisTranslation hd))^[n]) ⁻¹'
              cylinder t T) =
        (pottsIIDLabelMeasure d q).real (cylinder s S) *
          (pottsIIDLabelMeasure d q).real (cylinder t T) := by
  filter_upwards [pottsAxisFinsets_eventually_disjoint hd s t] with n hn
  rw [← pottsLabelShift_freeAxisTranslationPower hd n,
    pottsLabelShift_preimage_cylinder]
  let t' := t.image
    (fun x => (freeAxisTranslationPower hd n)⁻¹ • x)
  let T' : Set (t' -> Fin q) :=
    (fun (label : t' -> Fin q) (x : t) =>
      label ⟨(freeAxisTranslationPower hd n)⁻¹ • (x : Site d),
        Finset.mem_image_of_mem _ x.2⟩) ⁻¹' T
  have hT' : MeasurableSet T' := hT.preimage (by fun_prop)
  have hfactor := Percolation.bkc_infinitePi_disjoint_cylinder
    (fun _ : Site d => (PMF.uniformOfFintype (Fin q)).toMeasure)
    hS hT' hn
  have htranslated : (pottsIIDLabelMeasure d q).real (cylinder t' T') =
      (pottsIIDLabelMeasure d q).real (cylinder t T) := by
    rw [← pottsLabelShift_preimage_cylinder
      (freeAxisTranslationPower hd n) t T]
    exact (pottsIIDLabelMeasure_measurePreserving
      (q := q) (freeAxisTranslationPower hd n)).measureReal_preimage
        (MeasurableSet.cylinder t hT).nullMeasurableSet
  unfold pottsIIDLabelMeasure at htranslated ⊢
  rw [Measure.real, hfactor, ENNReal.toReal_mul,
    ← Measure.real, ← Measure.real, htranslated]

theorem pottsIIDLabel_exists_cylinder_symmDiff_lt {d q : Nat}
    [NeZero q] {A : Set (Site d -> Fin q)} (hA : MeasurableSet A)
    {epsilon : ENNReal} (hepsilon : 0 < epsilon) :
    ∃ C ∈ measurableCylinders (fun _ : Site d => Fin q),
      pottsIIDLabelMeasure d q (C ∆ A) < epsilon := by
  have hring : IsSetRing
      (measurableCylinders (fun _ : Site d => Fin q)) :=
    { empty_mem := empty_mem_measurableCylinders _
      union_mem := fun _ _ hs ht => union_mem_measurableCylinders hs ht
      diff_mem := fun _ _ hs ht => diff_mem_measurableCylinders hs ht }
  refine exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    hring ?_ generateFrom_measurableCylinders.symm hA hepsilon
  exact ⟨{Set.univ}, Set.countable_singleton _,
    by simpa using (univ_mem_measurableCylinders
      (fun _ : Site d => Fin q)), by simp⟩

set_option maxHeartbeats 2000000 in


theorem pottsIIDLabel_axis_mixingAgainst {d q : Nat} [NeZero q]
    (hd : 1 <= d) :
    MixingAgainst (pottsLabelShift (freeAxisTranslation hd))
      (pottsIIDLabelMeasure d q)
      (measurableCylinders (fun _ : Site d => Fin q)) := by
  classical
  intro A hA B hB
  rw [mem_measurableCylinders] at hB
  obtain ⟨t, T, hT, rfl⟩ := hB
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let delta := epsilon / 4
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨C, hCcyl, hCA⟩ :=
    pottsIIDLabel_exists_cylinder_symmDiff_lt (d := d) (q := q) hA
      (epsilon := ENNReal.ofReal delta) (by simpa using hdelta)
  rw [mem_measurableCylinders] at hCcyl
  obtain ⟨s, S, hS, rfl⟩ := hCcyl
  have hCmeas : MeasurableSet
      (cylinder (α := fun _ : Site d => Fin q) s S) :=
    MeasurableSet.cylinder s hS
  have hCAreal : (pottsIIDLabelMeasure d q).real
      (cylinder s S ∆ A) < delta := by
    have h := (ENNReal.toReal_lt_toReal
      (measure_ne_top (pottsIIDLabelMeasure d q) _) (by simp)).2 hCA
    rwa [ENNReal.toReal_ofReal hdelta.le] at h
  obtain ⟨N, hN⟩ := (eventually_atTop.1
    (pottsIIDLabel_cylinders_axis_factor hd s t S T hS hT))
  refine ⟨N, ?_⟩
  intro n hnN
  have hn := hN n hnN
  rw [Real.dist_eq]
  let Dn := ((pottsLabelShift (freeAxisTranslation hd))^[n]) ⁻¹'
    cylinder t T
  have hDn : MeasurableSet Dn :=
    (MeasurableSet.cylinder t hT).preimage
      ((pottsIIDLabelMeasure_measurePreserving (q := q)
        (freeAxisTranslation hd)).measurable.iterate n)
  have hinter : abs ((pottsIIDLabelMeasure d q).real (A ∩ Dn) -
      (pottsIIDLabelMeasure d q).real (cylinder s S ∩ Dn)) <=
      (pottsIIDLabelMeasure d q).real (cylinder s S ∆ A) := by
    calc
      abs ((pottsIIDLabelMeasure d q).real (A ∩ Dn) -
          (pottsIIDLabelMeasure d q).real (cylinder s S ∩ Dn)) <=
          (pottsIIDLabelMeasure d q).real
            ((A ∩ Dn) ∆ (cylinder s S ∩ Dn)) :=
        abs_measureReal_sub_le_measureReal_symmDiff
          (hA.inter hDn).nullMeasurableSet
          (hCmeas.inter hDn).nullMeasurableSet
      _ <= (pottsIIDLabelMeasure d q).real (cylinder s S ∆ A) := by
        rw [← Set.inter_symmDiff_distrib_right,
          symmDiff_comm A (cylinder s S)]
        exact measureReal_mono (Set.inter_subset_left) (by finiteness)
  have hmarg : abs ((pottsIIDLabelMeasure d q).real (cylinder s S) *
        (pottsIIDLabelMeasure d q).real (cylinder t T) -
      (pottsIIDLabelMeasure d q).real A *
        (pottsIIDLabelMeasure d q).real (cylinder t T)) <=
      (pottsIIDLabelMeasure d q).real (cylinder s S ∆ A) := by
    rw [← sub_mul, abs_mul]
    calc
      abs ((pottsIIDLabelMeasure d q).real (cylinder s S) -
          (pottsIIDLabelMeasure d q).real A) *
          abs ((pottsIIDLabelMeasure d q).real (cylinder t T)) <=
          (pottsIIDLabelMeasure d q).real (cylinder s S ∆ A) * 1 := by
        gcongr
        · exact abs_measureReal_sub_le_measureReal_symmDiff
            hCmeas.nullMeasurableSet hA.nullMeasurableSet
        · rw [abs_of_nonneg measureReal_nonneg]
          exact measureReal_le_one
      _ = (pottsIIDLabelMeasure d q).real (cylinder s S ∆ A) := mul_one _
  change abs ((pottsIIDLabelMeasure d q).real (A ∩ Dn) -
    (pottsIIDLabelMeasure d q).real A *
      (pottsIIDLabelMeasure d q).real (cylinder t T)) < epsilon
  rw [show (pottsIIDLabelMeasure d q).real (cylinder s S ∩ Dn) =
      (pottsIIDLabelMeasure d q).real (cylinder s S) *
        (pottsIIDLabelMeasure d q).real (cylinder t T) from hn] at hinter
  calc
    abs ((pottsIIDLabelMeasure d q).real (A ∩ Dn) -
        (pottsIIDLabelMeasure d q).real A *
          (pottsIIDLabelMeasure d q).real (cylinder t T)) <=
      abs ((pottsIIDLabelMeasure d q).real (A ∩ Dn) -
        (pottsIIDLabelMeasure d q).real (cylinder s S) *
          (pottsIIDLabelMeasure d q).real (cylinder t T)) +
      abs ((pottsIIDLabelMeasure d q).real (cylinder s S) *
        (pottsIIDLabelMeasure d q).real (cylinder t T) -
        (pottsIIDLabelMeasure d q).real A *
          (pottsIIDLabelMeasure d q).real (cylinder t T)) := abs_sub_le _ _ _
    _ <= 2 * (pottsIIDLabelMeasure d q).real (cylinder s S ∆ A) := by
      linarith
    _ < epsilon := by
      calc
        2 * (pottsIIDLabelMeasure d q).real (cylinder s S ∆ A) <
            2 * delta := mul_lt_mul_of_pos_left hCAreal (by norm_num)
        _ < epsilon := by dsimp [delta]; linarith


theorem freeInfiniteVolume_axisShift_ergodic_generalQ
    {d : Nat} (hd : 1 <= d) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    _root_.Ergodic
      (ConfigSpace.shift (freeAxisTranslation hd) :
        ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d)))
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  let mu := (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d))))
  have hti : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) mu :=
    fkgqt_freeIV_isTranslationInvariant hp hp1 hq
  refine ⟨hti (freeAxisTranslation hd), ⟨?_⟩⟩
  intro s hs hinv
  have hinvPow : forall n : Nat,
      ConfigSpace.shift (freeAxisTranslationPower hd n) ⁻¹' s = s := by
    intro n
    rw [shift_freeAxisTranslationPower]
    exact Function.IsFixedPt.preimage_iterate hinv n
  obtain ⟨t, ht, hae⟩ :=
    ati_sequenceInvariant_aeTail (fkTailEdgeWindow d)
      fkTailEdgeWindow_mono (freeAxisTranslationPower hd)
      (freeAxisTranslationPower_escape hd) hti s hs hinvPow
  rw [eventuallyConst_set']
  rcases freeInfiniteVolume_tail_trivial_generalQ hp hp1 hq t ht with
      ht0 | ht1
  · exact Or.inl (hae.trans (ae_eq_empty.mpr ht0))
  · right
    apply hae.trans
    rw [ae_eq_univ]
    rw [measure_compl ht.measurableSet (measure_ne_top mu t), ht1,
      measure_univ]
    simp


theorem freeInfiniteVolume_prod_pottsIIDLabel_axis_ergodic
    {d q : Nat} [NeZero q] (hd : 1 <= d) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) :
    let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    _root_.Ergodic
      (Prod.map
        (ConfigSpace.shift (freeAxisTranslation hd) :
          ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d)))
        (pottsLabelShift (freeAxisTranslation hd)))
      ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _).prod
        (pottsIIDLabelMeasure d q)) := by
  dsimp only
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let edgeMeasure :=
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) :
      Measure (ConfigSpace (Sym2 (Site d))))
  apply ergodic_prod_of_mixingAgainst
    (ConfigSpace.shift (freeAxisTranslation hd))
    (pottsLabelShift (freeAxisTranslation hd))
    (freeInfiniteVolume_axisShift_ergodic_generalQ hd hp hp1 hqR)
    (pottsIIDLabelMeasure_measurePreserving (q := q)
      (freeAxisTranslation hd))
    (measurableCylinders (fun _ : Site d => Fin q))
  · exact generateFrom_measurableCylinders
  · exact isPiSystem_measurableCylinders
  · exact ⟨fun _ => Set.univ,
      fun _ => univ_mem_measurableCylinders _, by rw [iUnion_const]⟩
  · intro B hB
    exact MeasurableSet.of_mem_measurableCylinders hB
  · exact pottsIIDLabel_axis_mixingAgainst hd


theorem freeInfiniteVolume_pottsClusterFactorInput_isErgodicFor
    {d q : Nat} [NeZero q] (hd : 1 <= d) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) :
    let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    IsErgodicFor pottsClusterFactorInputShift
      ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _).prod
        (pottsIIDLabelMeasure d q)) := by
  dsimp only
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let edgeMeasure :=
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) :
      Measure (ConfigSpace (Sym2 (Site d))))
  let sourceMeasure := edgeMeasure.prod (pottsIIDLabelMeasure d q)
  have hti : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) edgeMeasure :=
    fkgqt_freeIV_isTranslationInvariant hp hp1 hqR
  have haxis : _root_.Ergodic
      (Prod.map
        (ConfigSpace.shift (freeAxisTranslation hd) :
          ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d)))
        (pottsLabelShift (freeAxisTranslation hd))) sourceMeasure :=
    freeInfiniteVolume_prod_pottsIIDLabel_axis_ergodic hd hp hp1
  refine ⟨?_, ?_⟩
  · intro g
    have hprod := (hti g).prod
      (pottsIIDLabelMeasure_measurePreserving (q := q) g)
    convert hprod using 1
  · intro s hs hinv
    have hinvAxis : (Prod.map
        (ConfigSpace.shift (freeAxisTranslation hd) :
          ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d)))
        (pottsLabelShift (freeAxisTranslation hd))) ⁻¹' s = s := by
      simpa only [pottsClusterFactorInputShift, Prod.map_apply] using
        hinv (freeAxisTranslation hd)
    rcases haxis.toPreErgodic.prob_eq_zero_or_one hs hinvAxis with
      hzero | hone
    · exact Or.inl hzero
    · right
      simpa only [measure_univ] using hone


theorem freePottsClusterSumJointMeasure_isErgodicFor
    {d q : Nat} [NeZero q] (hd : 1 <= d) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (boundaryColor : Fin q) :
    let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    IsErgodicFor (pottsJointShift (d := d) (q := q))
      (pottsClusterSumJointMeasure (d := d) (q := q) boundaryColor
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _)) := by
  dsimp only
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))) :=
    freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR)
  exact pottsClusterSumJointMeasure_isErgodicFor
    (d := d) (q := q) boundaryColor edgeMeasure
    (freeInfiniteVolume_pottsClusterFactorInput_isErgodicFor
      (d := d) (q := q) hd hp hp1)


theorem freePottsClusterSumSpinMarginal_isErgodicFor
    {d q : Nat} [NeZero q] (hd : 1 <= d) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (boundaryColor : Fin q) :
    let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    IsErgodicFor (pottsSpinShift (d := d) (q := q))
      (Measure.map Prod.fst
        (pottsClusterSumJointMeasure (d := d) (q := q) boundaryColor
          (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _))) := by
  dsimp only
  let hqR : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  let edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))) :=
    freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR)
  exact pottsClusterSumSpinMarginal_isErgodicFor
    (d := d) (q := q) boundaryColor edgeMeasure
    (freePottsClusterSumJointMeasure_isErgodicFor
      (d := d) (q := q) hd hp hp1 boundaryColor)


end StatMech.FK
