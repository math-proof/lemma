/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentLaws.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentMixingErgodicity.Part2
import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
import Def.StatisticalMechanics.Code.FrontierB.CurrentTraceInsertion.Part3
open MeasureTheory
open scoped ENNReal BigOperators symmDiff


namespace StatMech.FrontierB

open Sharpness Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem forceInfiniteCurrentEdgePositive_apply_same
    {E : Type*} [DecidableEq E] (e : E) (m : InfiniteCurrentConfig E) :
    forceInfiniteCurrentEdgePositive e m e = if m e = 0 then 2 else m e := by
  by_cases h : m e = 0 <;> simp [forceInfiniteCurrentEdgePositive, h]

@[simp] theorem forceInfiniteCurrentEdgePositive_apply_of_ne
    {E : Type*} [DecidableEq E] (e f : E) (hfe : f ≠ e)
    (m : InfiniteCurrentConfig E) :
    forceInfiniteCurrentEdgePositive e m f = m f := by
  by_cases h : m e = 0 <;> simp [forceInfiniteCurrentEdgePositive, h, hfe]

theorem continuous_forceInfiniteCurrentEdgePositive
    {E : Type*} [DecidableEq E] (e : E) :
    Continuous (forceInfiniteCurrentEdgePositive e :
      InfiniteCurrentConfig E → InfiniteCurrentConfig E) := by
  refine continuous_pi fun f => ?_
  by_cases hfe : f = e
  · subst f
    simpa only [forceInfiniteCurrentEdgePositive_apply_same] using
      (continuous_of_discreteTopology
      (f := fun k : ℕ => if k = 0 then 2 else k)).comp
        (continuous_apply e : Continuous (fun m : InfiniteCurrentConfig E => m e))
  · simpa only [forceInfiniteCurrentEdgePositive_apply_of_ne e f hfe] using
      (continuous_apply f : Continuous (fun m : InfiniteCurrentConfig E => m f))

theorem currentTrace_forceInfiniteCurrentEdgePositive
    {E : Type*} [DecidableEq E] (e : E) (m : InfiniteCurrentConfig E) :
    currentTrace (forceInfiniteCurrentEdgePositive e m) =
      setOpen e (currentTrace m) := by
  funext f
  by_cases hfe : f = e
  · subst f
    by_cases hm : m e = 0
    · simp [currentTrace, forceInfiniteCurrentEdgePositive, setOpen, hm]
    · have hmpos : 0 < m e := Nat.pos_of_ne_zero hm
      simp [currentTrace, forceInfiniteCurrentEdgePositive, setOpen, hm, hmpos]
  · simp [currentTrace, forceInfiniteCurrentEdgePositive_apply_of_ne e f hfe,
      setOpen_of_ne hfe]

theorem superposedCurrentTrace_forceInfiniteCurrentEdgePositive_fst
    {E : Type*} [DecidableEq E] (e : E)
    (m n : InfiniteCurrentConfig E) :
    superposedCurrentTrace (forceInfiniteCurrentEdgePositive e m, n) =
      setOpen e (superposedCurrentTrace (m, n)) := by
  funext f
  by_cases hfe : f = e
  · subst f
    by_cases hm : m e = 0
    · simp [superposedCurrentTrace, forceInfiniteCurrentEdgePositive, hm,
        setOpen]
    · have hmpos : 0 < m e := Nat.pos_of_ne_zero hm
      simp [superposedCurrentTrace, forceInfiniteCurrentEdgePositive, hm,
        setOpen, hmpos]
  · simp [superposedCurrentTrace,
      forceInfiniteCurrentEdgePositive_apply_of_ne e f hfe,
      setOpen_of_ne hfe]

theorem forceInfiniteCurrentEdgePositive_extendBoxCurrent
    (d n : ℕ) (e : (StatMech.FK.boxGraph d n).edgeFinset)
    (m : EdgeCurrent (StatMech.FK.boxGraph d n)) :
    forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e)
        (extendBoxCurrent d n m) =
      extendBoxCurrent d n (forceCurrentEdgePositive (StatMech.FK.boxGraph d n) e m) := by
  funext f
  by_cases hfe : f = boxCurrentEdgeIncl d n e
  · subst f
    by_cases hm : m e = 0 <;>
      simp [forceInfiniteCurrentEdgePositive, forceCurrentEdgePositive, hm]
  · by_cases hfrange : f ∈ Set.range (boxCurrentEdgeIncl d n)
    · obtain ⟨g, rfl⟩ := hfrange
      have hge : g ≠ e := fun h => hfe (h ▸ rfl)
      simp [forceInfiniteCurrentEdgePositive_apply_of_ne _ _ hfe,
        forceCurrentEdgePositive_apply_of_ne _ _ _ hge]
    · rw [forceInfiniteCurrentEdgePositive_apply_of_ne _ _ hfe,
        extendBoxCurrent_outside d n m f hfrange,
        extendBoxCurrent_outside d n _ f hfrange]


theorem freeBoxCurrentMeasure_forceInfiniteCurrentEdgePositive_bound
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : (StatMech.FK.boxGraph d n).edgeFinset)
    (S : Set (InfiniteCurrentConfig (Sym2 (Site d)))) (hS : MeasurableSet S) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (freeBoxCurrentMeasure d n beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) ⁻¹' S) ≤
      (freeBoxCurrentMeasure d n beta hbeta.le : Measure _) S := by
  let G := StatMech.FK.boxGraph d n
  let p := sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => zero_le_one)
  let B := extendBoxCurrent d n ⁻¹' S
  have hbound := currentPMF_forceCurrentEdgePositive_event_bound G beta hbeta ∅
    (Ising.acr_currentSum_empty_pos G beta (fun _ => 1)) e B
  have hbound' : ENNReal.ofReal (currentTraceInsertionConstant beta) *
      (PMF.map (forceCurrentEdgePositive G e) p).toMeasure B ≤
        p.toMeasure B := by
    simpa only [p, sourcelessCurrentPMF] using hbound
  have hmap : (PMF.map (forceCurrentEdgePositive G e) p).toMeasure B =
      p.toMeasure (forceCurrentEdgePositive G e ⁻¹' B) :=
    PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete MeasurableSet.of_discrete
  rw [hmap] at hbound'
  have hpre : forceCurrentEdgePositive G e ⁻¹' B =
      extendBoxCurrent d n ⁻¹'
        (forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) ⁻¹' S) := by
    ext m
    simp only [Set.mem_preimage, B]
    rw [forceInfiniteCurrentEdgePositive_extendBoxCurrent]
  change ENNReal.ofReal (currentTraceInsertionConstant beta) *
      Measure.map (extendBoxCurrent d n) p.toMeasure
        (forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) ⁻¹' S) ≤
    Measure.map (extendBoxCurrent d n) p.toMeasure S
  rw [Measure.map_apply (measurable_extendBoxCurrent d n)
      (hS.preimage (continuous_forceInfiniteCurrentEdgePositive _).measurable),
    Measure.map_apply (measurable_extendBoxCurrent d n) hS,
    ← hpre]
  exact hbound'


theorem plusBoxCurrentMeasure_forceInfiniteCurrentEdgePositive_bound
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : (StatMech.FK.boxGraph d n).edgeFinset)
    (S : Set (InfiniteCurrentConfig (Sym2 (Site d)))) (hS : MeasurableSet S) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (plusBoxCurrentMeasure d n beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) ⁻¹' S) ≤
      (plusBoxCurrentMeasure d n beta hbeta.le : Measure _) S := by
  let G := StatMech.FK.boxGraph d n
  let p := boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => zero_le_one) (boxCurrentInterior d n)
  let B := extendBoxCurrent d n ⁻¹' S
  have hbound := boundaryCurrentPMF_forceCurrentEdgePositive_event_bound
    G beta hbeta (boxCurrentInterior d n) e B
  have hbound' : ENNReal.ofReal (currentTraceInsertionConstant beta) *
      (PMF.map (forceCurrentEdgePositive G e) p).toMeasure B ≤
        p.toMeasure B := by
    simpa only [p] using hbound
  have hmap : (PMF.map (forceCurrentEdgePositive G e) p).toMeasure B =
      p.toMeasure (forceCurrentEdgePositive G e ⁻¹' B) :=
    PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete MeasurableSet.of_discrete
  rw [hmap] at hbound'
  have hpre : forceCurrentEdgePositive G e ⁻¹' B =
      extendBoxCurrent d n ⁻¹'
        (forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) ⁻¹' S) := by
    ext m
    simp only [Set.mem_preimage, B]
    rw [forceInfiniteCurrentEdgePositive_extendBoxCurrent]
  change ENNReal.ofReal (currentTraceInsertionConstant beta) *
      Measure.map (extendBoxCurrent d n) p.toMeasure
        (forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) ⁻¹' S) ≤
    Measure.map (extendBoxCurrent d n) p.toMeasure S
  rw [Measure.map_apply (measurable_extendBoxCurrent d n)
      (hS.preimage (continuous_forceInfiniteCurrentEdgePositive _).measurable),
    Measure.map_apply (measurable_extendBoxCurrent d n) hS,
    ← hpre]
  exact hbound'


theorem eventually_boxCurrentEdgeIncl_eq
    (d : ℕ) (e : Sym2 (Site d))
    (he : e ∈ (hypercubicLattice d).edgeSet) :
    ∀ᶠ n in Filter.atTop, ∃ eb : (StatMech.FK.boxGraph d n).edgeFinset,
      boxCurrentEdgeIncl d n eb = e := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hadj : (hypercubicLattice d).Adj a b := by
        rw [← SimpleGraph.mem_edgeSet]
        exact he
      obtain ⟨N, hN⟩ := finite_subset_box ({a, b} : Set (Site d)) (Set.toFinite _)
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have ha : a ∈ box d n := box_mono d hn (hN (by simp))
      have hb : b ∈ box d n := box_mono d hn (hN (by simp))
      have himage : s(a, b) ∈ Finset.image (StatMech.FK.edgeIncl d n)
          (StatMech.FK.boxGraph d n).edgeFinset :=
        (StatMech.IsingFK.hbx_mem_image_edgeIncl_iff d n a b).2 ⟨ha, hb, hadj⟩
      rw [Finset.mem_image] at himage
      obtain ⟨f, hf, hfe⟩ := himage
      exact ⟨⟨f, hf⟩, hfe⟩

theorem infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_clopen_bound
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet)
    (C : Set (InfiniteCurrentConfig (Sym2 (Site d)))) (hC : IsClopen C) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive e ⁻¹' C) ≤
      (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _) C := by
  have hconv := freeBoxCurrentMeasure_tendsto_full d beta hbeta
  have hpreClopen := hC.preimage (continuous_forceInfiniteCurrentEdgePositive e)
  have hpre := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hconv hpreClopen
  have hbase := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hconv hC
  have hpreE := (ENNReal.tendsto_coe).2 hpre
  have hbaseE := (ENNReal.tendsto_coe).2 hbase
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hpreE hbaseE
  have hcpre : Filter.Tendsto
      (fun n => ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (freeBoxCurrentMeasure d n beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive e ⁻¹' C))
      Filter.atTop (nhds (ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive e ⁻¹' C))) :=
    ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (currentTraceInsertionConstant beta)) hpreE
      (Or.inr ENNReal.ofReal_ne_top)
  apply le_of_tendsto_of_tendsto hcpre hbaseE
  filter_upwards [eventually_boxCurrentEdgeIncl_eq d e he] with n hn
  obtain ⟨eb, heb⟩ := hn
  simpa only [heb] using
    (freeBoxCurrentMeasure_forceInfiniteCurrentEdgePositive_bound
      d n beta hbeta eb C hC.isOpen.measurableSet)

theorem infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_clopen_bound
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet)
    (C : Set (InfiniteCurrentConfig (Sym2 (Site d)))) (hC : IsClopen C) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (infinitePlusCurrentMeasure d beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive e ⁻¹' C) ≤
      (infinitePlusCurrentMeasure d beta hbeta.le : Measure _) C := by
  have hconv := plusBoxCurrentMeasure_tendsto_full d beta hbeta
  have hpreClopen := hC.preimage (continuous_forceInfiniteCurrentEdgePositive e)
  have hpre := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hconv hpreClopen
  have hbase := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hconv hC
  have hpreE := (ENNReal.tendsto_coe).2 hpre
  have hbaseE := (ENNReal.tendsto_coe).2 hbase
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hpreE hbaseE
  have hcpre : Filter.Tendsto
      (fun n => ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (plusBoxCurrentMeasure d n beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive e ⁻¹' C))
      Filter.atTop (nhds (ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (infinitePlusCurrentMeasure d beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive e ⁻¹' C))) :=
    ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (currentTraceInsertionConstant beta)) hpreE
      (Or.inr ENNReal.ofReal_ne_top)
  apply le_of_tendsto_of_tendsto hcpre hbaseE
  filter_upwards [eventually_boxCurrentEdgeIncl_eq d e he] with n hn
  obtain ⟨eb, heb⟩ := hn
  simpa only [heb] using
    (plusBoxCurrentMeasure_forceInfiniteCurrentEdgePositive_bound
      d n beta hbeta eb C hC.isOpen.measurableSet)

theorem isClopen_of_mem_currentMeasurableCylinders
    {E : Type*} (C : Set (InfiniteCurrentConfig E))
    (hC : C ∈ measurableCylinders (fun _ : E => ℕ)) : IsClopen C := by
  rw [mem_measurableCylinders] at hC
  obtain ⟨S, A, _, rfl⟩ := hC
  simpa only [currentCylinder, cylinder, Finset.restrict] using
    (isClopen_currentCylinder S A)

theorem infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_cylinder_real_bound
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet)
    (C : Set (InfiniteCurrentConfig (Sym2 (Site d))))
    (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => ℕ)) :
    currentTraceInsertionConstant beta *
        (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
          (forceInfiniteCurrentEdgePositive e ⁻¹' C) ≤
      (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real C := by
  have h := infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_clopen_bound
    d beta hbeta e he C (isClopen_of_mem_currentMeasurableCylinders C hC)
  have hreal := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr h
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (currentTraceInsertionConstant_pos hbeta).le] at hreal
  exact hreal

theorem infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_cylinder_real_bound
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet)
    (C : Set (InfiniteCurrentConfig (Sym2 (Site d))))
    (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => ℕ)) :
    currentTraceInsertionConstant beta *
        (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
          (forceInfiniteCurrentEdgePositive e ⁻¹' C) ≤
      (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real C := by
  have h := infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_clopen_bound
    d beta hbeta e he C (isClopen_of_mem_currentMeasurableCylinders C hC)
  have hreal := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr h
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (currentTraceInsertionConstant_pos hbeta).le] at hreal
  exact hreal


theorem currentModification_bound_of_cylinders
    {E : Type*} [Countable E]
    (mu : Measure (InfiniteCurrentConfig E)) [IsProbabilityMeasure mu]
    (f : InfiniteCurrentConfig E → InfiniteCurrentConfig E) (hf : Measurable f)
    (c : ℝ) (hc : 0 ≤ c)
    (hcyl : ∀ C ∈ measurableCylinders (fun _ : E => ℕ),
      c * mu.real (f ⁻¹' C) ≤ mu.real C)
    (A : Set (InfiniteCurrentConfig E)) (hA : MeasurableSet A) :
    c * mu.real (f ⁻¹' A) ≤ mu.real A := by
  let nu : Measure (InfiniteCurrentConfig E) := mu.map f
  let lam : Measure (InfiniteCurrentConfig E) := mu + nu
  have hfA : MeasurableSet (f ⁻¹' A) := hA.preimage hf
  refine le_of_forall_pos_le_add fun eps heps => ?_
  let delta : ℝ := eps / (c + 1)
  have hc1 : 0 < c + 1 := by linarith
  have hdelta : 0 < delta := div_pos heps hc1
  obtain ⟨C, hCmem, happrox⟩ := current_exists_cylinder_symmDiff_lt lam hA
    (epsilon := ENNReal.ofReal delta) (by simpa using hdelta)
  have hC : MeasurableSet C :=
    MeasurableSet.of_mem_measurableCylinders hCmem
  have hsd : MeasurableSet (C ∆ A) := hC.symmDiff hA
  have hlamReal : lam.real (C ∆ A) < delta := by
    have htop : lam (C ∆ A) ≠ ⊤ := measure_ne_top lam _
    have h := (ENNReal.toReal_lt_toReal htop (by simp)).2 happrox
    rwa [ENNReal.toReal_ofReal hdelta.le] at h
  have hmu_le : mu.real (C ∆ A) ≤ lam.real (C ∆ A) := by
    unfold Measure.real
    apply ENNReal.toReal_mono (measure_ne_top lam _)
    exact Measure.le_iff'.mp (Measure.le_add_right le_rfl) (C ∆ A)
  have hnu_le : nu.real (C ∆ A) ≤ lam.real (C ∆ A) := by
    unfold Measure.real
    apply ENNReal.toReal_mono (measure_ne_top lam _)
    exact Measure.le_iff'.mp (Measure.le_add_left le_rfl) (C ∆ A)
  have hmuDiff : |mu.real C - mu.real A| < delta :=
    lt_of_le_of_lt
      (abs_measureReal_sub_le_measureReal_symmDiff
        hC.nullMeasurableSet hA.nullMeasurableSet)
      (hmu_le.trans_lt hlamReal)
  have hnuMap : nu.real (C ∆ A) = mu.real (f ⁻¹' (C ∆ A)) := by
    unfold nu Measure.real
    rw [Measure.map_apply hf hsd]
  have hpreSd : f ⁻¹' (C ∆ A) = (f ⁻¹' C) ∆ (f ⁻¹' A) := by
    ext x
    simp
  have hnuDiff : |mu.real (f ⁻¹' C) - mu.real (f ⁻¹' A)| < delta := by
    have hpreC : MeasurableSet (f ⁻¹' C) := hC.preimage hf
    have habs : |mu.real (f ⁻¹' C) - mu.real (f ⁻¹' A)| ≤
        mu.real ((f ⁻¹' C) ∆ (f ⁻¹' A)) :=
      abs_measureReal_sub_le_measureReal_symmDiff
        hpreC.nullMeasurableSet hfA.nullMeasurableSet
    rw [← hpreSd, ← hnuMap] at habs
    exact lt_of_le_of_lt habs (hnu_le.trans_lt hlamReal)
  have hCbound := hcyl C hCmem
  obtain ⟨hmuLower, hmuUpper⟩ := abs_lt.mp hmuDiff
  obtain ⟨hnuLower, hnuUpper⟩ := abs_lt.mp hnuDiff
  dsimp [delta] at hmuLower hmuUpper hnuLower hnuUpper
  nlinarith [div_mul_cancel₀ eps (ne_of_gt hc1)]

theorem infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet) :
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).map
        (forceInfiniteCurrentEdgePositive e) ≪
      (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _) := by
  apply StatMech.FK.map_absolutelyContinuous_of_real_preimage_bound
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _)
    (forceInfiniteCurrentEdgePositive e)
    (continuous_forceInfiniteCurrentEdgePositive e).measurable
    (currentTraceInsertionConstant beta)
    (currentTraceInsertionConstant_pos hbeta)
  intro A hA
  exact currentModification_bound_of_cylinders
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _)
    (forceInfiniteCurrentEdgePositive e)
    (continuous_forceInfiniteCurrentEdgePositive e).measurable
    (currentTraceInsertionConstant beta)
    (currentTraceInsertionConstant_pos hbeta).le
    (infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_cylinder_real_bound
      d beta hbeta e he) A hA

theorem infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet) :
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).map
        (forceInfiniteCurrentEdgePositive e) ≪
      (infinitePlusCurrentMeasure d beta hbeta.le : Measure _) := by
  apply StatMech.FK.map_absolutelyContinuous_of_real_preimage_bound
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _)
    (forceInfiniteCurrentEdgePositive e)
    (continuous_forceInfiniteCurrentEdgePositive e).measurable
    (currentTraceInsertionConstant beta)
    (currentTraceInsertionConstant_pos hbeta)
  intro A hA
  exact currentModification_bound_of_cylinders
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _)
    (forceInfiniteCurrentEdgePositive e)
    (continuous_forceInfiniteCurrentEdgePositive e).measurable
    (currentTraceInsertionConstant beta)
    (currentTraceInsertionConstant_pos hbeta).le
    (infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_cylinder_real_bound
      d beta hbeta e he) A hA


theorem independentSuperposedTraceLaw_setOpen_absolutelyContinuous_of_fst
    {E : Type*} [Countable E] [DecidableEq E]
    (mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)) (e : E)
    (hmu : (mu : Measure _).map (forceInfiniteCurrentEdgePositive e) ≪
      (mu : Measure _)) :
    (independentSuperposedTraceLaw mu nu : Measure _).map
    (setOpen e) ≪
      (independentSuperposedTraceLaw mu nu : Measure _) := by
  let T : InfiniteCurrentConfig E × InfiniteCurrentConfig E →
      InfiniteCurrentConfig E × InfiniteCurrentConfig E :=
    Prod.map (forceInfiniteCurrentEdgePositive e) id
  have hTmeas : Measurable T :=
    (continuous_forceInfiniteCurrentEdgePositive e).measurable.prodMap measurable_id
  have hpair : (mu.prod nu : Measure _).map T ≪ (mu.prod nu : Measure _) := by
    change Measure.map (Prod.map (forceInfiniteCurrentEdgePositive e) id)
        ((mu : Measure (InfiniteCurrentConfig E)).prod
          (nu : Measure (InfiniteCurrentConfig E))) ≪
      (mu : Measure (InfiniteCurrentConfig E)).prod
        (nu : Measure (InfiniteCurrentConfig E))
    have hprod := hmu.prod
      (Measure.absolutelyContinuous_refl
        (nu : Measure (InfiniteCurrentConfig E)))
    have hmap := Measure.map_prod_map
      (mu : Measure (InfiniteCurrentConfig E))
      (nu : Measure (InfiniteCurrentConfig E))
      (continuous_forceInfiniteCurrentEdgePositive e).measurable measurable_id
    rw [← hmap]
    simpa only [Measure.map_id] using hprod
  have htrace := hpair.map continuous_superposedCurrentTrace.measurable
  have hsemiconj : (setOpen e) ∘ superposedCurrentTrace =
      superposedCurrentTrace ∘ T := by
    funext pair
    exact (superposedCurrentTrace_forceInfiniteCurrentEdgePositive_fst
      e pair.1 pair.2).symm
  change Measure.map (setOpen e)
      (Measure.map superposedCurrentTrace (mu.prod nu : Measure _)) ≪
    Measure.map superposedCurrentTrace (mu.prod nu : Measure _)
  rw [Measure.map_map (StatMech.FK.measurable_setOpen e)
      continuous_superposedCurrentTrace.measurable,
    hsemiconj,
    ← Measure.map_map continuous_superposedCurrentTrace.measurable hTmeas]
  exact htrace

theorem freeFreeSuperposedTraceLaw_setOpen_absolutelyContinuous
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet) :
    (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _).map
          (setOpen e) ≪
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _) :=
  independentSuperposedTraceLaw_setOpen_absolutelyContinuous_of_fst
    (infiniteFreeCurrentMeasure d beta hbeta.le)
    (infiniteFreeCurrentMeasure d beta hbeta.le) e
    (infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous
      d beta hbeta e he)

theorem freePlusSuperposedTraceLaw_setOpen_absolutelyContinuous
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet) :
    (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _).map
          (setOpen e) ≪
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _) :=
  independentSuperposedTraceLaw_setOpen_absolutelyContinuous_of_fst
    (infiniteFreeCurrentMeasure d beta hbeta.le)
    (infinitePlusCurrentMeasure d beta hbeta.le) e
    (infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous
      d beta hbeta e he)

theorem plusPlusSuperposedTraceLaw_setOpen_absolutelyContinuous
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet) :
    (independentSuperposedTraceLaw
        (infinitePlusCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _).map
          (setOpen e) ≪
      (independentSuperposedTraceLaw
        (infinitePlusCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _) :=
  independentSuperposedTraceLaw_setOpen_absolutelyContinuous_of_fst
    (infinitePlusCurrentMeasure d beta hbeta.le)
    (infinitePlusCurrentMeasure d beta hbeta.le) e
    (infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous
      d beta hbeta e he)


end StatMech.FrontierB
