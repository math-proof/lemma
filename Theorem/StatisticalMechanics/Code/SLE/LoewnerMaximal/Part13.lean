/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part12
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem loewnerMaximalMapsInverse_congr_time
    {W : ℝ → ℝ} (hW : Continuous W) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s = t) :
    loewnerMaximalMapsInverse hW hs = loewnerMaximalMapsInverse hW ht := by
  subst t
  congr


theorem loewnerMaximalMapsInverse_mem
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {y : ℂ} (hy : y ∈ upperHalfPlane) :
    loewnerMaximalMapsInverse hW ht y ∈ loewnerUnswallowedDomain W t := by
  rw [loewnerMaximalMapsInverse, dif_pos hy]
  exact (Classical.choose_spec
    (loewnerMaximalMaps_surjOn_upperHalfPlane hW ht hy)).1


theorem loewnerMaximalMaps_inverse
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {y : ℂ} (hy : y ∈ upperHalfPlane) :
    loewnerMaximalMaps W t (loewnerMaximalMapsInverse hW ht y) = y := by
  rw [loewnerMaximalMapsInverse, dif_pos hy]
  exact (Classical.choose_spec
    (loewnerMaximalMaps_surjOn_upperHalfPlane hW ht hy)).2


theorem eq_loewnerMaximalMapsInverse_of_mapsTo
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {x y : ℂ} (hx : x ∈ loewnerUnswallowedDomain W t)
    (hy : y ∈ upperHalfPlane) (hxy : loewnerMaximalMaps W t x = y) :
    x = loewnerMaximalMapsInverse hW ht y := by
  apply loewnerMaximalMaps_injOn hW ht hx
    (loewnerMaximalMapsInverse_mem hW ht hy)
  rw [hxy, loewnerMaximalMaps_inverse hW ht hy]


theorem exists_loewnerMaximalMaps_localRightInverse_of_lt_im_sq_div_sixteen
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {y : ℂ} (hy : 0 < y.im) (hlt : t < y.im ^ 2 / 16) :
    ∃ inv : ℂ → ℂ,
      ContinuousOn inv (closedBall y (y.im / 4)) ∧
        MapsTo inv (closedBall y (y.im / 4))
          (loewnerUnswallowedDomain W t) ∧
        ∀ v ∈ closedBall y (y.im / 4),
          loewnerMaximalMaps W t (inv v) = v := by
  let E : ℝ := y.im ^ 2 / 16
  have hE : 0 < E := by dsimp [E]; positivity
  have hltE : t < E := by simpa [E] using hlt
  obtain ⟨α, hα, C, hC⟩ := loewner_local_flow_chart hW hy t
  let inv : ℂ → ℂ := fun v ↦ α v 0
  have hinterval : Icc (0 : ℝ) (t + E) ⊆ Icc (t - E) (t + E) := by
    intro u hu
    exact ⟨by linarith [hu.1], hu.2⟩
  have hzeroInterval : (0 : ℝ) ∈ Icc (t - E) (t + E) := by
    constructor
    · linarith
    · positivity
  have hsolution :
      ∀ v ∈ closedBall y (y.im / 4),
        {g : LoewnerForwardSolution W (inv v) (t + E) // g.curve = α v} := by
    intro v hv
    obtain ⟨hend, hderiv, hstrip⟩ := hα v hv
    refine ⟨{
      curve := α v
      initial := rfl
      deriv := ?_
      upper := ?_ }, rfl⟩
    · intro u hu
      exact (hderiv u (hinterval hu)).mono hinterval
    · intro u hu
      exact loewnerStrip_subset_upperHalfPlane (by positivity) (hstrip u)
  refine ⟨inv, ?_, ?_, ?_⟩
  · exact (hC 0 hzeroInterval).continuousOn
  · intro v hv
    let g := (hsolution v hv).1
    have htotal : 0 < t + E := by positivity
    have hvUpper : inv v ∈ upperHalfPlane := by
      rw [← g.initial]
      exact g.upper 0 ⟨le_rfl, by positivity⟩
    have hbefore : IsBeforeLoewnerLifetime W (inv v) t :=
      (isBeforeLoewnerLifetime_iff_exists_admissible ht).2
        ⟨t + E, ⟨htotal, ⟨g⟩⟩, by linarith⟩
    exact ⟨hvUpper, hbefore⟩
  · intro v hv
    let g := (hsolution v hv).1
    have htotal : 0 < t + E := by positivity
    calc
      loewnerMaximalMaps W t (inv v) = g.curve t := by
        exact loewnerMaximalCurve_eq_forwardSolution htotal g
          ⟨ht, by linarith⟩
      _ = α v t := congrFun (hsolution v hv).2 t
      _ = v := (hα v hv).1


theorem continuousAt_loewnerMaximalMapsInverse_of_lt_im_sq_div_sixteen
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {y : ℂ} (hy : y ∈ upperHalfPlane) (hlt : t < y.im ^ 2 / 16) :
    ContinuousAt (loewnerMaximalMapsInverse hW ht) y := by
  have hypos : 0 < y.im := mem_upperHalfPlane.mp hy
  obtain ⟨inv, hinvContinuous, hinvMaps, hinvRight⟩ :=
    exists_loewnerMaximalMaps_localRightInverse_of_lt_im_sq_div_sixteen
      hW ht hypos hlt
  have hradius : 0 < y.im / 4 := by positivity
  have hball : closedBall y (y.im / 4) ∈ 𝓝 y :=
    closedBall_mem_nhds y hradius
  have hEq : loewnerMaximalMapsInverse hW ht =ᶠ[𝓝 y] inv := by
    filter_upwards [hball, isOpen_upperHalfPlane.mem_nhds hy] with v hvBall hvUpper
    exact (eq_loewnerMaximalMapsInverse_of_mapsTo hW ht
      (hinvMaps hvBall) hvUpper (hinvRight v hvBall)).symm
  exact (hinvContinuous y (mem_closedBall_self hradius.le)).continuousAt hball
    |>.congr_of_eventuallyEq hEq


theorem loewnerMaximalMaps_local_lipschitz_of_lt_im_sq_div_sixteen
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {z₀ : ℂ} (hz₀ : 0 < z₀.im) (hlt : t < z₀.im ^ 2 / 16) :
    ∃ C : ℝ≥0,
      closedBall z₀ (z₀.im / 4) ⊆ loewnerUnswallowedDomain W t ∧
        LipschitzOnWith C (loewnerMaximalMaps W t)
          (closedBall z₀ (z₀.im / 4)) := by
  let E : ℝ := z₀.im ^ 2 / 16
  have hE : 0 < E := by dsimp [E]; positivity
  have hδ : 0 < z₀.im / 2 := by positivity
  obtain ⟨α, hα, C, hC⟩ := loewner_local_flow_chart hW hz₀ 0
  have hinterval : Icc (0 : ℝ) (z₀.im ^ 2 / 16) ⊆
      Icc (0 - z₀.im ^ 2 / 16) (0 + z₀.im ^ 2 / 16) := by
    intro u hu
    exact ⟨by linarith [hu.1], by simpa using hu.2⟩
  let hsolution :
      ∀ w ∈ closedBall z₀ (z₀.im / 4),
        {g : LoewnerForwardSolution W w (z₀.im ^ 2 / 16) //
          g.curve = α w} := by
    intro w hw
    obtain ⟨hinit, hderiv, hstrip⟩ := hα w hw
    refine ⟨{
      curve := α w
      initial := by simpa using hinit
      deriv := ?_
      upper := ?_ }, rfl⟩
    · intro u hu
      exact (hderiv u (hinterval hu)).mono hinterval
    · intro u hu
      exact loewnerStrip_subset_upperHalfPlane hδ (hstrip u)
  have heq : EqOn (loewnerMaximalMaps W t) (fun w ↦ α w t)
      (closedBall z₀ (z₀.im / 4)) := by
    intro w hw
    calc
      loewnerMaximalMaps W t w =
          (hsolution w hw).1.curve t := by
        simpa only [loewnerMaximalMaps] using
          loewnerMaximalCurve_eq_forwardSolution (by simpa [E] using hE)
            (hsolution w hw).1 ⟨ht, hlt⟩
      _ = α w t := congrFun (hsolution w hw).2 t
  have hsub : closedBall z₀ (z₀.im / 4) ⊆ loewnerUnswallowedDomain W t := by
    intro w hw
    let g := (hsolution w hw).1
    have hwupper : w ∈ upperHalfPlane := by
      rw [← g.initial]
      exact g.upper 0 ⟨le_rfl, hE.le⟩
    have hbefore : IsBeforeLoewnerLifetime W w t :=
      (isBeforeLoewnerLifetime_iff_exists_admissible ht).2
        ⟨E, ⟨hE, ⟨g⟩⟩, by simpa [E] using hlt⟩
    exact ⟨hwupper, hbefore⟩
  refine ⟨C, hsub, ?_⟩
  have htchart : t ∈ Icc (-E) E := ⟨by linarith, by simpa [E] using hlt.le⟩
  have hslice := hC t (by simpa [E] using htchart)
  intro x hx y hy
  rw [heq hx, heq hy]
  exact hslice hx hy


theorem continuousAt_loewnerMaximalMaps_of_lt_im_sq_div_sixteen
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {z₀ : ℂ} (hz₀ : 0 < z₀.im) (hlt : t < z₀.im ^ 2 / 16) :
    ContinuousAt (loewnerMaximalMaps W t) z₀ := by
  obtain ⟨C, _, hC⟩ :=
    loewnerMaximalMaps_local_lipschitz_of_lt_im_sq_div_sixteen hW ht hz₀ hlt
  apply (hC.continuousOn z₀ (mem_closedBall_self (by positivity))).continuousAt
  exact closedBall_mem_nhds z₀ (by positivity)


theorem loewnerUnswallowedDomain_zero {W : ℝ → ℝ} (hW : Continuous W) :
    loewnerUnswallowedDomain W 0 = upperHalfPlane := by
  ext z
  constructor
  · exact fun hz ↦ hz.1
  · exact fun hz ↦ mem_loewnerUnswallowedDomain_zero hW hz


theorem loewnerMaximalMaps_satisfiesMaximalLoewnerEquation
    {W : ℝ → ℝ} (hW : Continuous W) :
    SatisfiesMaximalLoewnerEquation W (loewnerUnswallowedDomain W)
      (loewnerMaximalMaps W) := by
  refine ⟨loewnerUnswallowedDomain_zero hW, ?_, ?_, ?_⟩
  · intro z hz
    exact loewnerMaximalMaps_zero hW hz.1
  · intro z hz
    exact loewnerMaximalMaps_hasDerivWithinAt_zero hW hz.1
  · intro t ht z hz
    exact loewnerMaximalMaps_hasDerivAt ht hz


theorem loewnerMaximalMaps_regularAt_zero {W : ℝ → ℝ} (hW : Continuous W)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    loewnerUnswallowedDomain W 0 ∈ 𝓝 z ∧
      ContinuousAt (loewnerMaximalMaps W 0) z := by
  have hdomain : loewnerUnswallowedDomain W 0 ∈ 𝓝 z := by
    rw [loewnerUnswallowedDomain_zero hW]
    exact isOpen_upperHalfPlane.mem_nhds hz
  refine ⟨hdomain, continuousAt_id.congr_of_eventuallyEq ?_⟩
  filter_upwards [hdomain] with w hw
  simpa only [id_eq] using loewnerMaximalMaps_zero hW hw.1


theorem loewnerUnswallowedDomain_antitoneOn (W : ℝ → ℝ) :
    AntitoneOn (loewnerUnswallowedDomain W) (Ici (0 : ℝ)) := by
  intro s hs t ht hst z hz
  refine ⟨hz.1, hs, ?_⟩
  exact (ENNReal.ofReal_le_ofReal hst).trans_lt hz.2.2


theorem loewnerUnswallowedDomain_add_subset
    (W : ℝ → ℝ) {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) :
    loewnerUnswallowedDomain W (s + u) ⊆
      loewnerUnswallowedDomain W s ∩
        loewnerMaximalMaps W s ⁻¹'
          loewnerUnswallowedDomain (fun r ↦ W (s + r)) u := by
  intro z hz
  refine ⟨loewnerUnswallowedDomain_antitoneOn W hs (add_nonneg hs hu)
    (le_add_of_nonneg_right hu) hz, ?_⟩
  exact loewnerMaximalMaps_mem_shiftedUnswallowedDomain hs hu hz


theorem loewnerUnswallowedDomain_add_eq
    (W : ℝ → ℝ) {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) :
    loewnerUnswallowedDomain W (s + u) =
      loewnerUnswallowedDomain W s ∩
        loewnerMaximalMaps W s ⁻¹'
          loewnerUnswallowedDomain (fun r ↦ W (s + r)) u := by
  apply Subset.antisymm (loewnerUnswallowedDomain_add_subset W hs hu)
  rintro z ⟨hzs, hzu⟩
  let g := selectedLoewnerSolution hzs.2
  let A := selectedLoewnerDuration hzs.2
  have hA : 0 < A := (selectedLoewnerDuration_spec hzs.2).1.1
  have hsA : s < A := (selectedLoewnerDuration_spec hzs.2).2
  let gS : LoewnerForwardSolution W z s := g.restrict hsA.le
  let h₀ := selectedLoewnerSolution hzu.2
  let B := selectedLoewnerDuration hzu.2
  have hB : 0 < B := (selectedLoewnerDuration_spec hzu.2).1.1
  have huB : u < B := (selectedLoewnerDuration_spec hzu.2).2
  have hmax : loewnerMaximalMaps W s z = g.curve s := by
    exact loewnerMaximalCurve_eq_forwardSolution hA g ⟨hs, hsA⟩
  let h : LoewnerForwardSolution (fun r ↦ W (s + r)) (g.curve s) B := by
    rw [← hmax]
    exact h₀
  let gh : LoewnerForwardSolution W z (s + B) := gS.append h hs hB.le
  have hadmissible : IsLoewnerAdmissibleDuration W z (s + B) :=
    ⟨by linarith, ⟨gh⟩⟩
  have hbefore : IsBeforeLoewnerLifetime W z (s + u) :=
    (isBeforeLoewnerLifetime_iff_exists_admissible (add_nonneg hs hu)).2
      ⟨s + B, hadmissible, by linarith⟩
  exact ⟨hzs.1, hbefore⟩


theorem continuous_loewnerDriver_shift
    {W : ℝ → ℝ} (hW : Continuous W) (s : ℝ) :
    Continuous (fun r ↦ W (s + r)) :=
  hW.comp (continuous_const.add continuous_id)


theorem loewnerMaximalMapsInverse_add
    {W : ℝ → ℝ} (hW : Continuous W) {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u)
    {y : ℂ} (hy : y ∈ upperHalfPlane) :
    loewnerMaximalMapsInverse hW (add_nonneg hs hu) y =
      loewnerMaximalMapsInverse hW hs
        (loewnerMaximalMapsInverse
          (continuous_loewnerDriver_shift hW s) hu y) := by
  let Ws : ℝ → ℝ := fun r ↦ W (s + r)
  have hWs : Continuous Ws := hW.comp (continuous_const.add continuous_id)
  let a : ℂ := loewnerMaximalMapsInverse hWs hu y
  have haShift : a ∈ loewnerUnswallowedDomain Ws u :=
    loewnerMaximalMapsInverse_mem hWs hu hy
  have haUpper : a ∈ upperHalfPlane := haShift.1
  let x : ℂ := loewnerMaximalMapsInverse hW hs a
  have hxInitial : x ∈ loewnerUnswallowedDomain W s :=
    loewnerMaximalMapsInverse_mem hW hs haUpper
  have hxTotal : x ∈ loewnerUnswallowedDomain W (s + u) := by
    rw [loewnerUnswallowedDomain_add_eq W hs hu]
    refine ⟨hxInitial, ?_⟩
    change loewnerMaximalMaps W s x ∈ loewnerUnswallowedDomain Ws u
    rw [loewnerMaximalMaps_inverse hW hs haUpper]
    exact haShift
  have hxMap : loewnerMaximalMaps W (s + u) x = y := by
    rw [loewnerMaximalMaps_flow hs hu hxTotal,
      loewnerMaximalMaps_inverse hW hs haUpper,
      loewnerMaximalMaps_inverse hWs hu hy]
  exact (eq_loewnerMaximalMapsInverse_of_mapsTo hW (add_nonneg hs hu)
    hxTotal hy hxMap).symm


theorem continuousAt_loewnerMaximalMapsInverse_add
    {W : ℝ → ℝ} (hW : Continuous W) {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u)
    {y : ℂ} (hy : y ∈ upperHalfPlane)
    (hfirst : ContinuousAt (loewnerMaximalMapsInverse hW hs)
      (loewnerMaximalMapsInverse
        (continuous_loewnerDriver_shift hW s) hu y))
    (hsecond : ContinuousAt
      (loewnerMaximalMapsInverse
        (continuous_loewnerDriver_shift hW s) hu) y) :
    ContinuousAt (loewnerMaximalMapsInverse hW (add_nonneg hs hu)) y := by
  have hcomp : ContinuousAt
      (fun v ↦ loewnerMaximalMapsInverse hW hs
        (loewnerMaximalMapsInverse
          (continuous_loewnerDriver_shift hW s) hu v)) y :=
    hfirst.comp' hsecond
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlane.mem_nhds hy] with v hv
  exact loewnerMaximalMapsInverse_add hW hs hu hv


theorem continuousAt_loewnerMaximalMapsInverse_steps
    {W : ℝ → ℝ} (hW : Continuous W) {u : ℝ} (hu : 0 ≤ u)
    (n : ℕ) {y : ℂ} (hy : y ∈ upperHalfPlane)
    (hshort : u < y.im ^ 2 / 16) :
    ContinuousAt
      (loewnerMaximalMapsInverse hW
        (mul_nonneg (Nat.cast_nonneg n) hu)) y := by
  induction n generalizing y with
  | zero =>
      have hypos : 0 < y.im := mem_upperHalfPlane.mp hy
      let hzero : 0 ≤ (0 : ℝ) * u := by simp
      have hbase :=
        continuousAt_loewnerMaximalMapsInverse_of_lt_im_sq_div_sixteen
          hW hzero hy (by simpa using (show 0 < y.im ^ 2 / 16 by positivity))
      rw [loewnerMaximalMapsInverse_congr_time hW hzero
        (mul_nonneg (Nat.cast_nonneg 0) hu) (by norm_num)] at hbase
      exact hbase
  | succ n ih =>
      let s : ℝ := (n : ℝ) * u
      have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg n) hu
      let Ws : ℝ → ℝ := fun r ↦ W (s + r)
      have hWs : Continuous Ws := hW.comp (continuous_const.add continuous_id)
      let a : ℂ := loewnerMaximalMapsInverse hWs hu y
      have haShift : a ∈ loewnerUnswallowedDomain Ws u :=
        loewnerMaximalMapsInverse_mem hWs hu hy
      have haUpper : a ∈ upperHalfPlane := haShift.1
      have haZero : a ∈ loewnerUnswallowedDomain Ws 0 :=
        loewnerUnswallowedDomain_antitoneOn Ws
          (show (0 : ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
          (show u ∈ Ici 0 from mem_Ici.mpr hu) hu haShift
      have him : y.im ≤ a.im := by
        have hant := loewnerMaximalCurve_im_antitoneOn haZero.2 haShift.2 hu
        change (loewnerMaximalMaps Ws u a).im ≤
          (loewnerMaximalMaps Ws 0 a).im at hant
        rw [loewnerMaximalMaps_inverse hWs hu hy,
          loewnerMaximalMaps_zero hWs haUpper] at hant
        exact hant
      have hshortA : u < a.im ^ 2 / 16 := by
        have hy0 : 0 ≤ y.im := (mem_upperHalfPlane.mp hy).le
        calc
          u < y.im ^ 2 / 16 := hshort
          _ ≤ a.im ^ 2 / 16 := by nlinarith
      have hfirst : ContinuousAt (loewnerMaximalMapsInverse hW hs) a :=
        ih haUpper hshortA
      have hsecond : ContinuousAt (loewnerMaximalMapsInverse hWs hu) y :=
        continuousAt_loewnerMaximalMapsInverse_of_lt_im_sq_div_sixteen
          hWs hu hy hshort
      have hadd := continuousAt_loewnerMaximalMapsInverse_add hW hs hu hy
        (by simpa [Ws] using hfirst) (by simpa [Ws] using hsecond)
      have htime : (((n + 1 : ℕ) : ℝ) * u) = s + u := by
        simp only [s, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      rw [loewnerMaximalMapsInverse_congr_time hW
        (mul_nonneg (Nat.cast_nonneg (n + 1)) hu) (add_nonneg hs hu) htime]
      exact hadd


theorem continuousAt_loewnerMaximalMapsInverse
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {y : ℂ} (hy : y ∈ upperHalfPlane) :
    ContinuousAt (loewnerMaximalMapsInverse hW ht) y := by
  have hypos : 0 < y.im := mem_upperHalfPlane.mp hy
  obtain ⟨n, hn⟩ := exists_nat_gt (16 * t / y.im ^ 2)
  have hquot : 0 ≤ 16 * t / y.im ^ 2 := by positivity
  have hn0 : 0 < (n : ℝ) := hquot.trans_lt hn
  let u : ℝ := t / (n : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hnu : (n : ℝ) * u = t := by
    dsimp [u]
    field_simp
  have hshort : u < y.im ^ 2 / 16 := by
    rw [div_lt_iff₀ hn0]
    have hmul : 16 * t < (n : ℝ) * y.im ^ 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hypos)).mp hn
    nlinarith
  have hcont := continuousAt_loewnerMaximalMapsInverse_steps
    hW hu n hy hshort
  rw [← loewnerMaximalMapsInverse_congr_time hW
    (mul_nonneg (Nat.cast_nonneg n) hu) ht hnu]
  exact hcont


theorem loewnerMaximalMaps_regularAt_add_of_lt_im_sq_div_sixteen
    {W : ℝ → ℝ} (hW : Continuous W) {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u)
    {z : ℂ} (hz : z ∈ loewnerUnswallowedDomain W (s + u))
    (hregular : loewnerUnswallowedDomain W s ∈ 𝓝 z ∧
      ContinuousAt (loewnerMaximalMaps W s) z)
    (hshort : u < (loewnerMaximalMaps W s z).im ^ 2 / 16) :
    loewnerUnswallowedDomain W (s + u) ∈ 𝓝 z ∧
      ContinuousAt (loewnerMaximalMaps W (s + u)) z := by
  let Ws : ℝ → ℝ := fun r ↦ W (s + r)
  have hWs : Continuous Ws :=
    hW.comp (continuous_const.add continuous_id)
  have hzs : z ∈ loewnerUnswallowedDomain W s :=
    loewnerUnswallowedDomain_antitoneOn W hs (add_nonneg hs hu)
      (le_add_of_nonneg_right hu) hz
  let y : ℂ := loewnerMaximalMaps W s z
  have hy : 0 < y.im :=
    mem_upperHalfPlane.mp (loewnerMaximalMaps_mem_upperHalfPlane hzs)
  obtain ⟨C, hball, hLip⟩ :=
    loewnerMaximalMaps_local_lipschitz_of_lt_im_sq_div_sixteen
      hWs hu hy hshort
  let B : Set ℂ := closedBall y (y.im / 4)
  have hB : B ∈ 𝓝 y := closedBall_mem_nhds y (by positivity)
  have hpre : loewnerMaximalMaps W s ⁻¹' B ∈ 𝓝 z :=
    hregular.2 hB
  have hdomain : loewnerUnswallowedDomain W (s + u) ∈ 𝓝 z := by
    apply mem_of_superset (inter_mem hregular.1 hpre)
    intro w hw
    rw [loewnerUnswallowedDomain_add_eq W hs hu]
    exact ⟨hw.1, hball hw.2⟩
  refine ⟨hdomain, ?_⟩
  have hshiftContinuous :
      ContinuousAt (loewnerMaximalMaps Ws u) y :=
    (hLip.continuousOn y (mem_closedBall_self (by positivity))).continuousAt hB
  have hcomp : ContinuousAt
      (fun w ↦ loewnerMaximalMaps Ws u (loewnerMaximalMaps W s w)) z := by
    simpa only [Function.comp_def] using
      Filter.Tendsto.comp hshiftContinuous hregular.2
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hdomain] with w hw
  exact loewnerMaximalMaps_flow hs hu hw


theorem loewnerMaximalMaps_regularAt
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ∈ loewnerUnswallowedDomain W t) :
    loewnerUnswallowedDomain W t ∈ 𝓝 z ∧
      ContinuousAt (loewnerMaximalMaps W t) z := by
  let δ : ℝ := (loewnerMaximalMaps W t z).im
  have hδ : 0 < δ :=
    mem_upperHalfPlane.mp (loewnerMaximalMaps_mem_upperHalfPlane hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (16 * t / δ ^ 2)
  have hquot : 0 ≤ 16 * t / δ ^ 2 := by positivity
  have hn0 : 0 < (n : ℝ) := hquot.trans_lt hn
  let u : ℝ := t / (n : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hnu : (n : ℝ) * u = t := by
    dsimp [u]
    field_simp
  have hushort : u < δ ^ 2 / 16 := by
    rw [div_lt_iff₀ hn0]
    have hmul : 16 * t < (n : ℝ) * δ ^ 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hδ)).mp hn
    nlinarith
  have htime (k : ℕ) (hk : k ≤ n) :
      0 ≤ (k : ℝ) * u ∧ (k : ℝ) * u ≤ t := by
    refine ⟨mul_nonneg (Nat.cast_nonneg k) hu, ?_⟩
    rw [← hnu]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hu
  have hsurvives (k : ℕ) (hk : k ≤ n) :
      z ∈ loewnerUnswallowedDomain W ((k : ℝ) * u) := by
    exact loewnerUnswallowedDomain_antitoneOn W (htime k hk).1 ht
      (htime k hk).2 hz
  have hind : ∀ k : ℕ, k ≤ n →
      loewnerUnswallowedDomain W ((k : ℝ) * u) ∈ 𝓝 z ∧
        ContinuousAt (loewnerMaximalMaps W ((k : ℝ) * u)) z := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa using loewnerMaximalMaps_regularAt_zero hW hz.1
    | succ k ih =>
        intro hkn
        have hk : k ≤ n := (Nat.le_succ k).trans hkn
        have hs := (htime k hk).1
        have hznext := hsurvives (k + 1) hkn
        have hstepTime :
            ((k + 1 : ℕ) : ℝ) * u = (k : ℝ) * u + u := by
          rw [Nat.cast_add, Nat.cast_one]
          ring
        have hzadd :
            z ∈ loewnerUnswallowedDomain W ((k : ℝ) * u + u) := by
          rw [hstepTime] at hznext
          exact hznext
        have him : δ ≤ (loewnerMaximalMaps W ((k : ℝ) * u) z).im := by
          exact loewnerMaximalCurve_im_antitoneOn
            (hsurvives k hk).2 hz.2 (htime k hk).2
        have hshort :
            u < (loewnerMaximalMaps W ((k : ℝ) * u) z).im ^ 2 / 16 := by
          calc
            u < δ ^ 2 / 16 := hushort
            _ ≤ (loewnerMaximalMaps W ((k : ℝ) * u) z).im ^ 2 / 16 := by
              gcongr
        have hregadd :=
          loewnerMaximalMaps_regularAt_add_of_lt_im_sq_div_sixteen
            hW hs hu hzadd (ih hk) hshort
        rw [← hstepTime] at hregadd
        exact hregadd
  have hnreg := hind n le_rfl
  rwa [hnu] at hnreg


theorem isOpen_loewnerUnswallowedDomain
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsOpen (loewnerUnswallowedDomain W t) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  exact (loewnerMaximalMaps_regularAt hW ht hz).1


theorem continuousOn_loewnerMaximalMaps
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (loewnerMaximalMaps W t) (loewnerUnswallowedDomain W t) := by
  intro z hz
  exact (loewnerMaximalMaps_regularAt hW ht hz).2.continuousWithinAt


theorem continuousOn_loewnerMaximalMapsInverse
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (loewnerMaximalMapsInverse hW ht) upperHalfPlane := by
  intro y hy
  exact (continuousAt_loewnerMaximalMapsInverse hW ht hy).continuousWithinAt


end StatMech.SLE
