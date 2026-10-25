/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductFinite
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductApprox.Part5
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


universe w


universe z wF wG

theorem functionalFamilyBKR_of_finiteCoordinateFactors_and_dual
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (F G : Set E → (∀ e, S e) → ℝ)
    (fF : ∀ K, FiniteCoordinateFactorOn.{u, v, wF} K (F K))
    (fG : ∀ K, FiniteCoordinateFactorOn.{u, v, wG} K (G K))
    (hF0 : ∀ K y, 0 ≤ (fF K).H y) (hG0 : ∀ K y, 0 ≤ (fG K).H y) :
    (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G x)
        ∂Measure.pi mu) ≤
        (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x) ∂Measure.pi mu) *
        ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x) ∂Measure.pi mu ∧
      (∫⁻ p, ENNReal.ofReal
          (piFunctionalFamilyDisjointMaxAt F G p.1 p.2)
          ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
        ∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x)
          ∂Measure.pi mu := by
  classical
  letI fFComponentFintype : ∀ K e, Fintype ((fF K).T e) :=
    fun K e => (fF K).fintype_T e
  letI fGComponentFintype : ∀ K e, Fintype ((fG K).T e) :=
    fun K e => (fG K).fintype_T e
  letI fFComponentMeasurableSpace : ∀ K e, MeasurableSpace ((fF K).T e) :=
    fun K e => (fF K).measurableSpace_T e
  letI fGComponentMeasurableSpace : ∀ K e, MeasurableSpace ((fG K).T e) :=
    fun K e => (fG K).measurableSpace_T e
  letI fFComponentMeasurableSingleton :
      ∀ K e, MeasurableSingletonClass ((fF K).T e) :=
    fun K e => (fF K).measurableSingleton_T e
  letI fGComponentMeasurableSingleton :
      ∀ K e, MeasurableSingletonClass ((fG K).T e) :=
    fun K e => (fG K).measurableSingleton_T e
  let T : E → Type (max u wF wG) := fun e =>
    ((K : Set E) → (fF K).T e) × ((K : Set E) → (fG K).T e)
  letI instF : ∀ e, Fintype (T e) := fun _ => inferInstance
  letI instM : ∀ e, MeasurableSpace (T e) := fun _ => inferInstance
  letI instS : ∀ e, MeasurableSingletonClass (T e) := fun _ => inferInstance
  let q : ∀ e, S e → T e := fun e x =>
    (fun K => (fF K).q e x, fun K => (fG K).q e x)
  let Fbar : Set E → (∀ e, T e) → ℝ := fun K y =>
    (fF K).H (fun e => (y e).1 K)
  let Gbar : Set E → (∀ e, T e) → ℝ := fun K y =>
    (fG K).H (fun e => (y e).2 K)
  have hq : ∀ e, Measurable (q e) := by
    intro e
    apply Measurable.prod
    · apply measurable_pi_lambda
      intro K
      exact (fF K).measurable_q e
    · apply measurable_pi_lambda
      intro K
      exact (fG K).measurable_q e
  have hFbar0 : ∀ K y, 0 ≤ Fbar K y := fun K y => hF0 K _
  have hGbar0 : ∀ K y, 0 ≤ Gbar K y := fun K y => hG0 K _
  have hFbarDep : ∀ K, PiDependsOn K (Fbar K) := by
    intro K y z hyz
    apply (fF K).dependsOn_H
    intro e he
    exact congrArg (fun z => z.1 K) (hyz e he)
  have hGbarDep : ∀ K, PiDependsOn K (Gbar K) := by
    intro K y z hyz
    apply (fG K).dependsOn_H
    intro e he
    exact congrArg (fun z => z.2 K) (hyz e he)
  have hcore := @functionalFamilyBKR_finiteFactor_and_dual
    E _ _ S _ T instM instF instS mu _ q hq Fbar Gbar
      hFbar0 hGbar0 hFbarDep hGbarDep
  have hFcomp : ∀ K x, Fbar K (fun e => q e (x e)) = F K x := by
    intro K x
    exact (congrFun (fF K).eq_comp x).symm
  have hGcomp : ∀ K x, Gbar K (fun e => q e (x e)) = G K x := by
    intro K x
    exact (congrFun (fG K).eq_comp x).symm
  simpa only [piFunctionalFamilyDisjointMax,
    piFunctionalFamilyDisjointMaxAt, piFunctionalFamilyMax,
    hFcomp, hGcomp] using hcore

theorem FiniteCoordinateFactorOn.measurable
    {K : Set E} {h : (∀ e, S e) → ℝ} (f : FiniteCoordinateFactorOn K h) :
    Measurable h := by
  letI : ∀ e, Fintype (f.T e) := f.fintype_T
  letI : ∀ e, MeasurableSpace (f.T e) := f.measurableSpace_T
  letI : ∀ e, MeasurableSingletonClass (f.T e) := f.measurableSingleton_T
  rw [f.eq_comp]
  exact (measurable_of_finite f.H).comp
    (measurable_pi_lambda _ fun e =>
      (f.measurable_q e).comp (measurable_pi_apply e))

theorem FiniteCoordinateFactorOn.nonneg
    {K : Set E} {h : (∀ e, S e) → ℝ} (f : FiniteCoordinateFactorOn K h) :
    ∀ x, 0 ≤ h x := by
  intro x
  rw [f.eq_comp]
  exact f.nonneg_H _

theorem exists_finiteFactor_approx_simple
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (K : Set E) (s : SimpleFunc (∀ e, S e) ℝ)
    (hs0 : ∀ x, 0 ≤ s x) {C : ℝ} (hsC : ∀ x, s x ≤ C)
    (hsdep : PiDependsOn K s) {eps : ℝ≥0∞} (heps : 0 < eps) :
    ∃ (t : (∀ e, S e) → ℝ)
      (f : FiniteCoordinateFactorOn.{u, v, 0} K t),
      (∀ x, t x ≤ C) ∧
      Measure.pi mu {x | t x ≠ s x} < eps := by
  classical
  letI : ∀ e, Nonempty (S e) := fun e => nonempty_of_isProbabilityMeasure (mu e)
  let values : Finset ℝ := insert 0 s.range
  let I := {v : ℝ // v ∈ values}
  letI : Fintype I := values.fintypeCoeSort
  have hI : (Finset.univ : Finset I).Nonempty :=
    ⟨⟨0, Finset.mem_insert_self 0 s.range⟩, Finset.mem_univ _⟩
  have hvalue0 : ∀ v : I, 0 ≤ v.1 := by
    intro v
    rcases Finset.mem_insert.mp v.2 with hv | hv
    · simpa [hv]
    · obtain ⟨x, hx⟩ := SimpleFunc.mem_range.mp hv
      simpa [← hx] using hs0 x
  have hvalueC : ∀ v : I, v.1 ≤ C := by
    intro v
    rcases Finset.mem_insert.mp v.2 with hv | hv
    · simpa [hv] using le_trans (hs0 (Classical.choice
          (nonempty_of_isProbabilityMeasure (Measure.pi mu)))) (hsC _)
    · obtain ⟨x, hx⟩ := SimpleFunc.mem_range.mp hv
      simpa [← hx] using hsC x
  obtain ⟨delta, hdelta0, hdeltasum⟩ :=
    ENNReal.exists_pos_sum_of_countable' heps.ne' I
  let A : I → Set (∀ e, S e) := fun v => {x | s x = v.1}
  have hAmeas : ∀ v, MeasurableSet (A v) := fun v => by
    change MeasurableSet (s ⁻¹' ({v.1} : Set ℝ))
    exact s.measurableSet_fiber v.1
  have hAdep : ∀ v, PiSetDependsOn K (A v) := by
    intro v x y hxy
    have hsxy := hsdep hxy
    simp only [A, Set.mem_setOf_eq]
    rw [hsxy]
  have happ : ∀ v : I, ∃ B,
      IsFiniteCoordinateSet B ∧ PiSetDependsOn K B ∧
        Measure.pi mu (B ∆ A v) < delta v := fun v =>
    exists_finiteCoordinateSet_dependsOn_symmDiff_lt
      mu K (hAmeas v) (hAdep v) (hdelta0 v)
  choose B hBfin hBdep hBerr using happ
  let a : I → (∀ e, S e) → ℝ := fun v =>
    (B v).indicator (fun _ => v.1)
  let fa : ∀ v, FiniteCoordinateFactorOn.{u, v, 0} K (a v) := fun v =>
    finiteCoordinateFactorOn_piece K (hBfin v) (hBdep v) v.1 (hvalue0 v)
  let t : (∀ e, S e) → ℝ := fun x =>
    (Finset.univ : Finset I).sup' hI (fun v => a v x)
  let f : FiniteCoordinateFactorOn.{u, v, 0} K t :=
    finiteCoordinateFactorOn_sup' hI K a fa
  refine ⟨t, f, ?_, ?_⟩
  · intro x
    unfold t
    apply Finset.sup'_le
    intro v _
    by_cases hv : x ∈ B v
    · simpa [a, hv] using hvalueC v
    · simpa [a, hv] using le_trans (hvalue0 v) (hvalueC v)
  · let Bad : Set (∀ e, S e) := ⋃ v ∈ (Finset.univ : Finset I), B v ∆ A v
    have hsubset : {x | t x ≠ s x} ⊆ Bad := by
      intro x hx
      by_contra hxBad
      have hmatch : ∀ v : I, (x ∈ B v ↔ s x = v.1) := by
        intro v
        have hn : x ∉ B v ∆ A v := by
          intro hv
          apply hxBad
          exact Set.mem_iUnion₂.mpr ⟨v, Finset.mem_univ v, hv⟩
        rw [Set.mem_symmDiff] at hn
        simp only [A, Set.mem_setOf_eq] at hn
        tauto
      have ht : t x = s x := by
        apply le_antisymm
        · unfold t
          apply Finset.sup'_le
          intro v _
          by_cases hv : x ∈ B v
          · simpa [a, hv, (hmatch v).mp hv]
          · simpa [a, hv] using hs0 x
        · let v : I := ⟨s x, Finset.mem_insert_of_mem
              (SimpleFunc.mem_range.mpr ⟨x, rfl⟩)⟩
          calc
            s x = (v : ℝ) := rfl
            _ = a v x := by
              have hv : x ∈ B v := (hmatch v).mpr rfl
              exact (Set.indicator_of_mem hv (fun _ => (v : ℝ))).symm
            _ ≤ t x := Finset.le_sup' (fun z : I => a z x) (Finset.mem_univ v)
      exact hx ht
    calc
      Measure.pi mu {x | t x ≠ s x} ≤ Measure.pi mu Bad := measure_mono hsubset
      _ ≤ ∑ v ∈ (Finset.univ : Finset I), Measure.pi mu (B v ∆ A v) :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ v ∈ (Finset.univ : Finset I), delta v :=
        Finset.sum_le_sum fun v _ => (hBerr v).le
      _ ≤ ∑' v : I, delta v := ENNReal.sum_le_tsum _
      _ < eps := hdeltasum

theorem exists_finiteFactor_approx_bounded
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (K : Set E) (h : (∀ e, S e) → ℝ) (hh : Measurable h)
    (hh0 : ∀ x, 0 ≤ h x) {C : ℝ} (hhC : ∀ x, h x ≤ C)
    (hhdep : PiDependsOn K h) :
    ∃ (t : ℕ → (∀ e, S e) → ℝ)
        (f : ∀ n, FiniteCoordinateFactorOn.{u, v, 0} K (t n)),
      (∀ n x, t n x ≤ C) ∧
      ∀ᵐ x ∂Measure.pi mu, Tendsto (fun n => t n x) atTop (𝓝 (h x)) := by
  classical
  let simple : ℕ → SimpleFunc (∀ e, S e) ℝ := fun n =>
    SimpleFunc.approxOn h hh (Set.range h ∪ {0}) 0 (by simp) n
  have hs0 : ∀ n x, 0 ≤ simple n x := by
    intro n x
    exact SimpleFunc.approxOn_range_nonneg hh0 n x
  have hsC : ∀ n x, simple n x ≤ C := by
    intro n x
    have hx := SimpleFunc.approxOn_mem hh (s := Set.range h ∪ {0})
      (y₀ := 0) (by simp) n x
    rcases hx with hx | hx
    · obtain ⟨y, hy⟩ := hx
      rw [← hy]
      exact hhC y
    · rw [Set.mem_singleton_iff.mp hx]
      exact le_trans (hh0 x) (hhC x)
  have hsdep : ∀ n, PiDependsOn K (simple n) := by
    intro n x y hxy
    have hhy := hhdep hxy
    simp only [simple, SimpleFunc.approxOn, SimpleFunc.coe_comp, Function.comp_apply]
    rw [hhy]
  obtain ⟨eps, heps0, hepssum⟩ :=
    ENNReal.exists_pos_sum_of_countable' (by norm_num : (1 : ℝ≥0∞) ≠ 0) ℕ
  have happ : ∀ n, ∃ (t : (∀ e, S e) → ℝ)
      (f : FiniteCoordinateFactorOn.{u, v, 0} K t),
      (∀ x, t x ≤ C) ∧ Measure.pi mu {x | t x ≠ simple n x} < eps n :=
    fun n => exists_finiteFactor_approx_simple mu K (simple n)
      (hs0 n) (hsC n) (hsdep n) (heps0 n)
  choose t f htC herr using happ
  refine ⟨t, f, htC, ?_⟩
  have herrsum : (∑' n, Measure.pi mu {x | t n x ≠ simple n x}) ≠ ∞ := by
    apply ne_top_of_lt
    exact (ENNReal.tsum_le_tsum fun n => (herr n).le).trans_lt hepssum
  have heventually := ae_eventually_notMem herrsum
  filter_upwards [heventually] with x hx
  have hsconv : Tendsto (fun n => simple n x) atTop (𝓝 (h x)) :=
    SimpleFunc.tendsto_approxOn hh (s := Set.range h ∪ {0})
      (y₀ := 0) (by simp)
        (subset_closure (Set.mem_union_left {0} ⟨x, rfl⟩))
  apply hsconv.congr'
  filter_upwards [hx] with n hn
  exact (not_not.mp hn).symm

theorem measurableFamilyBKR_bounded_and_dual
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (F G : Set E → (∀ e, S e) → ℝ)
    (hFm : ∀ K, Measurable (F K)) (hGm : ∀ K, Measurable (G K))
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hFdep : ∀ K, PiDependsOn K (F K))
    (hGdep : ∀ K, PiDependsOn K (G K))
    (C D : ℝ) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hFC : ∀ K x, F K x ≤ C) (hGD : ∀ K x, G K x ≤ D) :
    (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G x)
        ∂Measure.pi mu) ≤
        (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x) ∂Measure.pi mu) *
        ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x) ∂Measure.pi mu ∧
      (∫⁻ p, ENNReal.ofReal
          (piFunctionalFamilyDisjointMaxAt F G p.1 p.2)
          ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
        ∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x)
          ∂Measure.pi mu := by
  classical
  have happF : ∀ K, ∃ (t : ℕ → (∀ e, S e) → ℝ)
      (f : ∀ n, FiniteCoordinateFactorOn.{u, v, 0} K (t n)),
      (∀ n x, t n x ≤ C) ∧
      ∀ᵐ x ∂Measure.pi mu, Tendsto (fun n => t n x) atTop (𝓝 (F K x)) :=
    fun K => exists_finiteFactor_approx_bounded mu K (F K) (hFm K)
      (hF0 K) (hFC K) (hFdep K)
  have happG : ∀ K, ∃ (t : ℕ → (∀ e, S e) → ℝ)
      (f : ∀ n, FiniteCoordinateFactorOn.{u, v, 0} K (t n)),
      (∀ n x, t n x ≤ D) ∧
      ∀ᵐ x ∂Measure.pi mu, Tendsto (fun n => t n x) atTop (𝓝 (G K x)) :=
    fun K => exists_finiteFactor_approx_bounded mu K (G K) (hGm K)
      (hG0 K) (hGD K) (hGdep K)
  choose Fn fFn hFnC hconvF using happF
  choose Gn fGn hGnD hconvG using happG
  let Fapp : ℕ → Set E → (∀ e, S e) → ℝ := fun n K => Fn K n
  let Gapp : ℕ → Set E → (∀ e, S e) → ℝ := fun n K => Gn K n
  have hineq : ∀ n,
      (∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyDisjointMax (Fapp n) (Gapp n) x)
          ∂Measure.pi mu) ≤
          (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (Fapp n) x)
            ∂Measure.pi mu) *
          ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (Gapp n) x)
            ∂Measure.pi mu ∧
        (∫⁻ p, ENNReal.ofReal
            (piFunctionalFamilyDisjointMaxAt (Fapp n) (Gapp n) p.1 p.2)
            ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
          ∫⁻ x, ENNReal.ofReal
            (piFunctionalFamilyMax (Fapp n) x *
              piFunctionalFamilyMax (Gapp n) x)
            ∂Measure.pi mu := by
    intro n
    exact functionalFamilyBKR_of_finiteCoordinateFactors_and_dual
      mu (Fapp n) (Gapp n) (fun K => fFn K n) (fun K => fGn K n)
        (fun K => (fFn K n).nonneg_H) (fun K => (fGn K n).nonneg_H)
  apply measurableFamilyBKR_of_bounded_ae_limit mu Fapp Gapp F G
    C D hC0 hD0
  · intro n K
    exact (fFn K n).measurable
  · intro n K
    exact (fGn K n).measurable
  · exact hFm
  · exact hGm
  · intro n K
    exact (fFn K n).nonneg
  · intro n K
    exact (fGn K n).nonneg
  · exact hF0
  · exact hG0
  · intro n K
    exact hFnC K n
  · intro n K
    exact hGnD K n
  · exact hFC
  · exact hGD
  · intro K
    exact hconvF K
  · intro K
    exact hconvG K
  · exact hineq

end StatMech.FrontierA
