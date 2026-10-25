/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part5
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.FKMixingClose
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
open MeasureTheory Set Filter Topology SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace FK

open StatMech.Lattice ConfigSpace

variable {d : ℕ}


theorem boxRestrictLE_setOpen {N m : ℕ} (hNm : N ≤ m)
    (eb : Sym2 (boxVerts d N)) (omega : ConfigSpace (Sym2 (boxVerts d m))) :
    boxRestrictLE d hNm (setOpen (innerEdgeLE d hNm eb) omega) =
      setOpen eb (boxRestrictLE d hNm omega) := by
  funext x
  by_cases hx : x = eb
  · subst x
    simp [boxRestrictLE]
  · have himg : innerEdgeLE d hNm x ≠ innerEdgeLE d hNm eb :=
      fun heq => hx (dfi_innerEdgeLE_injective d hNm heq)
    rw [boxRestrictLE, setOpen_of_ne himg, setOpen_of_ne hx]
    rfl


theorem boxRestrict_setOpen (N : ℕ) (eb : Sym2 (boxVerts d N))
    (omega : ConfigSpace (Sym2 (Site d))) :
    boxRestrict d N (setOpen (edgeIncl d N eb) omega) =
      setOpen eb (boxRestrict d N omega) := by
  funext x
  by_cases hx : x = eb
  · subst x
    simp [boxRestrict]
  · have himg : edgeIncl d N x ≠ edgeIncl d N eb :=
      fun heq => hx (edgeIncl_injective d N heq)
    rw [boxRestrict, setOpen_of_ne himg, setOpen_of_ne hx]
    rfl


theorem boxRestrictLE_setClosed {N m : ℕ} (hNm : N ≤ m)
    (eb : Sym2 (boxVerts d N)) (omega : ConfigSpace (Sym2 (boxVerts d m))) :
    boxRestrictLE d hNm (setClosed (innerEdgeLE d hNm eb) omega) =
      setClosed eb (boxRestrictLE d hNm omega) := by
  funext x
  by_cases hx : x = eb
  · subst x
    simp [boxRestrictLE]
  · have himg : innerEdgeLE d hNm x ≠ innerEdgeLE d hNm eb :=
      fun heq => hx (dfi_innerEdgeLE_injective d hNm heq)
    rw [boxRestrictLE, setClosed_of_ne himg, setClosed_of_ne hx]
    rfl


theorem boxRestrict_setClosed (N : ℕ) (eb : Sym2 (boxVerts d N))
    (omega : ConfigSpace (Sym2 (Site d))) :
    boxRestrict d N (setClosed (edgeIncl d N eb) omega) =
      setClosed eb (boxRestrict d N omega) := by
  funext x
  by_cases hx : x = eb
  · subst x
    simp [boxRestrict]
  · have himg : edgeIncl d N x ≠ edgeIncl d N eb :=
      fun heq => hx (edgeIncl_injective d N heq)
    rw [boxRestrict, setClosed_of_ne himg, setClosed_of_ne hx]
    rfl


theorem wiredFinite_singleOpen_preimage_bound
    (N m : ℕ) (hNm : N ≤ m) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S)) ≤
      (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  classical
  let em := innerEdgeLE d hNm eb
  let T := boxRestrictLE d hNm ⁻¹' S
  let eta : ConfigSpace ↥({em} : Finset (Sym2 (boxVerts d m))) := fun _ => true
  have hset : setPattern ({em} : Finset (Sym2 (boxVerts d m))) eta = setOpen em := by
    funext omega x
    by_cases hx : x = em
    · subst x
      simp [setPattern, eta]
    · rw [setPattern_of_not_mem eta (by simpa using hx), setOpen_of_ne hx]
  have hpreT : boxRestrictLE d hNm ⁻¹' (setOpen eb ⁻¹' S) = setOpen em ⁻¹' T := by
    ext omega
    simp only [Set.mem_preimage, T, em]
    rw [boxRestrictLE_setOpen]
  have hevent : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext omega
    simp only [Set.mem_preimage, T, boxRestrictLE_boxRestrict]
  have hpreEvent : boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S) =
      boxRestrict d m ⁻¹' (setOpen em ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage, T, em]
    rw [boxRestrictLE_setOpen, boxRestrictLE_boxRestrict]
  have hmeasT : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  have hmeasPre : MeasurableSet (boxRestrict d m ⁻¹' (setOpen em ⁻¹' T)) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [hevent, hpreEvent,
    fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1
      (zero_lt_one.trans_le hq) T hmeasT,
    fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1
      (zero_lt_one.trans_le hq) (setOpen em ⁻¹' T) hmeasPre]
  have hbound := cFE_pow_mul_bcPreimage_le_event (boxGraph d m)
    (boundaryCliqueGraph (boxBoundary d m)) hp hp1 hq ({em} : Finset _)
    eta T
  rw [hset] at hbound
  simpa only [Finset.card_singleton, pow_one, bcProb_clique_eq_wiredFkProb] using hbound


theorem freeFinite_singleOpen_preimage_bound
    (N m : ℕ) (hNm : N ≤ m) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S)) ≤
      (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  classical
  let em := innerEdgeLE d hNm eb
  let T := boxRestrictLE d hNm ⁻¹' S
  let eta : ConfigSpace ↥({em} : Finset (Sym2 (boxVerts d m))) := fun _ => true
  have hset : setPattern ({em} : Finset (Sym2 (boxVerts d m))) eta = setOpen em := by
    funext omega x
    by_cases hx : x = em
    · subst x
      simp [setPattern, eta]
    · rw [setPattern_of_not_mem eta (by simpa using hx), setOpen_of_ne hx]
  have hevent : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext omega
    simp only [Set.mem_preimage, T, boxRestrictLE_boxRestrict]
  have hpreEvent : boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S) =
      boxRestrict d m ⁻¹' (setOpen em ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage, T, em]
    rw [boxRestrictLE_setOpen, boxRestrictLE_boxRestrict]
  have hmeasT : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  have hmeasPre : MeasurableSet (boxRestrict d m ⁻¹' (setOpen em ⁻¹' T)) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [hevent, hpreEvent,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (zero_lt_one.trans_le hq) T hmeasT,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (zero_lt_one.trans_le hq)
      (setOpen em ⁻¹' T) hmeasPre]
  have hbound := cFE_pow_mul_bcPreimage_le_event (boxGraph d m)
    (⊥ : SimpleGraph (boxVerts d m)) hp hp1 hq ({em} : Finset _) eta T
  rw [hset] at hbound
  simpa only [Finset.card_singleton, pow_one, bcProb_bot_eq_fkProb] using hbound


theorem wiredFinite_singleClosed_preimage_bound
    (N m : ℕ) (hNm : N ≤ m) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S)) ≤
      (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  classical
  let em := innerEdgeLE d hNm eb
  let T := boxRestrictLE d hNm ⁻¹' S
  let eta : ConfigSpace ↥({em} : Finset (Sym2 (boxVerts d m))) := fun _ => false
  have hset : setPattern ({em} : Finset (Sym2 (boxVerts d m))) eta = setClosed em := by
    funext omega x
    by_cases hx : x = em
    · subst x
      simp [setPattern, eta]
    · rw [setPattern_of_not_mem eta (by simpa using hx), setClosed_of_ne hx]
  have hevent : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext omega
    simp only [Set.mem_preimage, T, boxRestrictLE_boxRestrict]
  have hpreEvent : boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S) =
      boxRestrict d m ⁻¹' (setClosed em ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage, T, em]
    rw [boxRestrictLE_setClosed, boxRestrictLE_boxRestrict]
  have hmeasT : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  have hmeasPre : MeasurableSet (boxRestrict d m ⁻¹' (setClosed em ⁻¹' T)) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [hevent, hpreEvent,
    fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1
      (zero_lt_one.trans_le hq) T hmeasT,
    fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1
      (zero_lt_one.trans_le hq) (setClosed em ⁻¹' T) hmeasPre]
  have hbound := cFE_pow_mul_bcPreimage_le_event (boxGraph d m)
    (boundaryCliqueGraph (boxBoundary d m)) hp hp1 hq ({em} : Finset _)
    eta T
  rw [hset] at hbound
  simpa only [Finset.card_singleton, pow_one, bcProb_clique_eq_wiredFkProb] using hbound


theorem freeFinite_singleClosed_preimage_bound
    (N m : ℕ) (hNm : N ≤ m) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S)) ≤
      (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  classical
  let em := innerEdgeLE d hNm eb
  let T := boxRestrictLE d hNm ⁻¹' S
  let eta : ConfigSpace ↥({em} : Finset (Sym2 (boxVerts d m))) := fun _ => false
  have hset : setPattern ({em} : Finset (Sym2 (boxVerts d m))) eta = setClosed em := by
    funext omega x
    by_cases hx : x = em
    · subst x
      simp [setPattern, eta]
    · rw [setPattern_of_not_mem eta (by simpa using hx), setClosed_of_ne hx]
  have hevent : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext omega
    simp only [Set.mem_preimage, T, boxRestrictLE_boxRestrict]
  have hpreEvent : boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S) =
      boxRestrict d m ⁻¹' (setClosed em ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage, T, em]
    rw [boxRestrictLE_setClosed, boxRestrictLE_boxRestrict]
  have hmeasT : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  have hmeasPre : MeasurableSet (boxRestrict d m ⁻¹' (setClosed em ⁻¹' T)) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [hevent, hpreEvent,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (zero_lt_one.trans_le hq) T hmeasT,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (zero_lt_one.trans_le hq)
      (setClosed em ⁻¹' T) hmeasPre]
  have hbound := cFE_pow_mul_bcPreimage_le_event (boxGraph d m)
    (⊥ : SimpleGraph (boxVerts d m)) hp hp1 hq ({em} : Finset _) eta T
  rw [hset] at hbound
  simpa only [Finset.card_singleton, pow_one, bcProb_bot_eq_fkProb] using hbound


theorem wiredInfinite_singleOpen_cylinder_bound
    (N : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S)) ≤
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  obtain ⟨phi, hphi, hconv⟩ :=
    wiredInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  have hpre := hconv.tendsto_real_of_isClopen
    (fkWiredLimit_isClopen_preimage N (setOpen eb ⁻¹' S))
  have hbase := hconv.tendsto_real_of_isClopen
    (fkWiredLimit_isClopen_preimage N S)
  have hc : Tendsto (fun _ : ℕ => cFE p q) atTop (𝓝 (cFE p q)) := tendsto_const_nhds
  have hlhs := hc.mul hpre
  apply le_of_tendsto_of_tendsto hlhs hbase
  filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop N)] with n hn
  exact wiredFinite_singleOpen_preimage_bound N (phi n) hn hp hp1 hq eb S


theorem freeInfinite_singleOpen_cylinder_bound
    (N : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S)) ≤
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  obtain ⟨phi, hphi, hconv⟩ :=
    freeInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  have hpre := hconv.tendsto_real_of_isClopen
    (fkFreeLimit_isClopen_preimage N (setOpen eb ⁻¹' S))
  have hbase := hconv.tendsto_real_of_isClopen
    (fkFreeLimit_isClopen_preimage N S)
  have hc : Tendsto (fun _ : ℕ => cFE p q) atTop (𝓝 (cFE p q)) := tendsto_const_nhds
  have hlhs := hc.mul hpre
  apply le_of_tendsto_of_tendsto hlhs hbase
  filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop N)] with n hn
  exact freeFinite_singleOpen_preimage_bound N (phi n) hn hp hp1 hq eb S


theorem wiredInfinite_singleClosed_cylinder_bound
    (N : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S)) ≤
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  obtain ⟨phi, hphi, hconv⟩ :=
    wiredInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  have hpre := hconv.tendsto_real_of_isClopen
    (fkWiredLimit_isClopen_preimage N (setClosed eb ⁻¹' S))
  have hbase := hconv.tendsto_real_of_isClopen
    (fkWiredLimit_isClopen_preimage N S)
  have hc : Tendsto (fun _ : ℕ => cFE p q) atTop (𝓝 (cFE p q)) := tendsto_const_nhds
  apply le_of_tendsto_of_tendsto (hc.mul hpre) hbase
  filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop N)] with n hn
  exact wiredFinite_singleClosed_preimage_bound N (phi n) hn hp hp1 hq eb S


theorem freeInfinite_singleClosed_cylinder_bound
    (N : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S)) ≤
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  obtain ⟨phi, hphi, hconv⟩ :=
    freeInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  have hpre := hconv.tendsto_real_of_isClopen
    (fkFreeLimit_isClopen_preimage N (setClosed eb ⁻¹' S))
  have hbase := hconv.tendsto_real_of_isClopen
    (fkFreeLimit_isClopen_preimage N S)
  have hc : Tendsto (fun _ : ℕ => cFE p q) atTop (𝓝 (cFE p q)) := tendsto_const_nhds
  apply le_of_tendsto_of_tendsto (hc.mul hpre) hbase
  filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop N)] with n hn
  exact freeFinite_singleClosed_preimage_bound N (phi n) hn hp hp1 hq eb S


theorem setPattern_insert_eq
    {V : Type*} [DecidableEq V] {I : Finset (Sym2 V)} {e : Sym2 V}
    (he : e ∉ I) (eta : ConfigSpace ↥(insert e I))
    (psi : ConfigSpace (Sym2 V)) :
    let etaI : ConfigSpace ↥I := fun x => eta ⟨x, Finset.mem_insert_of_mem x.2⟩
    setPattern (insert e I) eta psi =
      if eta ⟨e, Finset.mem_insert_self e I⟩ then
        setOpen e (setPattern I etaI psi)
      else setClosed e (setPattern I etaI psi) := by
  dsimp only
  funext x
  by_cases heta : eta ⟨e, Finset.mem_insert_self e I⟩ = true
  · simp only [heta, if_true]
    by_cases hxe : x = e
    · subst x
      simp [setPattern, he, heta]
    · by_cases hxI : x ∈ I
      · rw [setOpen_of_ne hxe]
        simp [setPattern, hxI, hxe]
      · rw [setOpen_of_ne hxe]
        simp [setPattern, hxI, hxe]
  · have heta0 : eta ⟨e, Finset.mem_insert_self e I⟩ = false :=
      Bool.eq_false_of_not_eq_true heta
    simp only [heta0, Bool.false_eq_true, if_false]
    by_cases hxe : x = e
    · subst x
      simp [setPattern, he, heta0]
    · by_cases hxI : x ∈ I
      · rw [setClosed_of_ne hxe]
        simp [setPattern, hxI, hxe]
      · rw [setClosed_of_ne hxe]
        simp [setPattern, hxI, hxe]


theorem wiredInfinite_pattern_cylinder_bound
    (N : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 (boxVerts d N))) (eta : ConfigSpace ↥I)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q ^ I.card *
        (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setPattern I eta ⁻¹' S)) ≤
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  classical
  induction I using Finset.induction generalizing S with
  | empty =>
      simp only [Finset.card_empty, pow_zero, one_mul]
      have hset : setPattern ∅ eta = id := by
        funext psi
        exact setPattern_empty eta psi
      rw [hset]
      rfl
  | @insert e I he ih =>
      let etaI : ConfigSpace ↥I := fun x => eta ⟨x, Finset.mem_insert_of_mem x.2⟩
      have hdecomp := setPattern_insert_eq he eta
      rw [Finset.card_insert_of_notMem he, pow_succ]
      by_cases heta : eta ⟨e, Finset.mem_insert_self e I⟩ = true
      · have hpre : setPattern (insert e I) eta ⁻¹' S =
            setPattern I etaI ⁻¹' (setOpen e ⁻¹' S) := by
          ext psi
          simp only [Set.mem_preimage, hdecomp psi, heta, if_true, etaI]
        rw [hpre]
        have hih := ih etaI (setOpen e ⁻¹' S)
        have hone := wiredInfinite_singleOpen_cylinder_bound N hp hp1 hq e S
        have hc : 0 ≤ cFE p q := (cFE_pos hp hp1 hq).le
        calc
          cFE p q ^ I.card * cFE p q *
              (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setOpen e ⁻¹' S))) =
              cFE p q * (cFE p q ^ I.card *
                (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                  (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setOpen e ⁻¹' S)))) := by ring
          _ ≤ cFE p q *
              (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setOpen e ⁻¹' S)) :=
            mul_le_mul_of_nonneg_left hih hc
          _ ≤ _ := hone
      · have heta0 : eta ⟨e, Finset.mem_insert_self e I⟩ = false :=
          Bool.eq_false_of_not_eq_true heta
        have hpre : setPattern (insert e I) eta ⁻¹' S =
            setPattern I etaI ⁻¹' (setClosed e ⁻¹' S) := by
          ext psi
          simp only [Set.mem_preimage, hdecomp psi, heta0, Bool.false_eq_true,
            if_false, etaI]
        rw [hpre]
        have hih := ih etaI (setClosed e ⁻¹' S)
        have hclosed := wiredInfinite_singleClosed_cylinder_bound N hp hp1 hq e S
        have hc : 0 ≤ cFE p q := (cFE_pos hp hp1 hq).le
        calc
          cFE p q ^ I.card * cFE p q *
              (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setClosed e ⁻¹' S))) =
              cFE p q * (cFE p q ^ I.card *
                (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                  (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setClosed e ⁻¹' S)))) := by ring
          _ ≤ cFE p q *
              (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setClosed e ⁻¹' S)) :=
            mul_le_mul_of_nonneg_left hih hc
          _ ≤ _ := hclosed


theorem freeInfinite_pattern_cylinder_bound
    (N : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 (boxVerts d N))) (eta : ConfigSpace ↥I)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q ^ I.card *
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setPattern I eta ⁻¹' S)) ≤
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  classical
  induction I using Finset.induction generalizing S with
  | empty =>
      simp only [Finset.card_empty, pow_zero, one_mul]
      have hset : setPattern ∅ eta = id := by
        funext psi
        exact setPattern_empty eta psi
      rw [hset]
      rfl
  | @insert e I he ih =>
      let etaI : ConfigSpace ↥I := fun x => eta ⟨x, Finset.mem_insert_of_mem x.2⟩
      have hdecomp := setPattern_insert_eq he eta
      rw [Finset.card_insert_of_notMem he, pow_succ]
      by_cases heta : eta ⟨e, Finset.mem_insert_self e I⟩ = true
      · have hpre : setPattern (insert e I) eta ⁻¹' S =
            setPattern I etaI ⁻¹' (setOpen e ⁻¹' S) := by
          ext psi
          simp only [Set.mem_preimage, hdecomp psi, heta, if_true, etaI]
        rw [hpre]
        have hih := ih etaI (setOpen e ⁻¹' S)
        have hone := freeInfinite_singleOpen_cylinder_bound N hp hp1 hq e S
        have hc : 0 ≤ cFE p q := (cFE_pos hp hp1 hq).le
        calc
          cFE p q ^ I.card * cFE p q *
              (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setOpen e ⁻¹' S))) =
              cFE p q * (cFE p q ^ I.card *
                (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                  (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setOpen e ⁻¹' S)))) := by ring
          _ ≤ cFE p q *
              (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setOpen e ⁻¹' S)) :=
            mul_le_mul_of_nonneg_left hih hc
          _ ≤ _ := hone
      · have heta0 : eta ⟨e, Finset.mem_insert_self e I⟩ = false :=
          Bool.eq_false_of_not_eq_true heta
        have hpre : setPattern (insert e I) eta ⁻¹' S =
            setPattern I etaI ⁻¹' (setClosed e ⁻¹' S) := by
          ext psi
          simp only [Set.mem_preimage, hdecomp psi, heta0, Bool.false_eq_true,
            if_false, etaI]
        rw [hpre]
        have hih := ih etaI (setClosed e ⁻¹' S)
        have hclosed := freeInfinite_singleClosed_cylinder_bound N hp hp1 hq e S
        have hc : 0 ≤ cFE p q := (cFE_pos hp hp1 hq).le
        calc
          cFE p q ^ I.card * cFE p q *
              (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setClosed e ⁻¹' S))) =
              cFE p q * (cFE p q ^ I.card *
                (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                  (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setClosed e ⁻¹' S)))) := by ring
          _ ≤ cFE p q *
              (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setClosed e ⁻¹' S)) :=
            mul_le_mul_of_nonneg_left hih hc
          _ ≤ _ := hclosed


end FK
end StatMech
