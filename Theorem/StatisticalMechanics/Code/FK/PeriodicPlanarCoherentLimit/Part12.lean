/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part12
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

variable [Countable V]


omit [Countable V] in
theorem PeriodicGraph.exists_bufferedLevel_edges (P : PeriodicGraph V)
    (T : Finset (Sym2 V)) :
    ∃ N, ∀ e ∈ T, e ∈ Set.range (P.edgeIncl (P.bufferedRadius N)) := by
  classical
  obtain ⟨N, hN⟩ := P.finite_subset_orbitBox (PeriodicGraph.edgeVertexFinset T)
  refine ⟨N, ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxmem : x ∈ PeriodicGraph.edgeVertexFinset T := by
        simp only [PeriodicGraph.edgeVertexFinset, Finset.mem_biUnion]
        exact ⟨s(x, y), he, by simp⟩
      have hymem : y ∈ PeriodicGraph.edgeVertexFinset T := by
        simp only [PeriodicGraph.edgeVertexFinset, Finset.mem_biUnion]
        exact ⟨s(x, y), he, by simp⟩
      let xb : P.BufferedVertex N :=
        ⟨x, P.orbitBox_mono (P.id_le_bufferedRadius N) (hN x hxmem)⟩
      let yb : P.BufferedVertex N :=
        ⟨y, P.orbitBox_mono (P.id_le_bufferedRadius N) (hN y hymem)⟩
      exact ⟨s(xb, yb), rfl⟩

theorem PeriodicGraph.bufferedCylinder_real_eq_signedSum
    (P : PeriodicGraph V)
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 V))) (N : ℕ)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N))))
    {I : Type*} (t : Finset I) (c : I → ℝ)
    (A : I → Set (ConfigSpace (Sym2 (P.BufferedVertex N))))
    (hexp : S.indicator (1 : ConfigSpace (Sym2 (P.BufferedVertex N)) → ℝ) =
      ∑ i ∈ t, c i • (A i).indicator 1) :
    (mu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) =
      ∑ i ∈ t, c i *
        (mu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N (A i)) := by
  have hpoint : (P.bufferedCylinder N S).indicator
        (1 : ConfigSpace (Sym2 V) → ℝ) =
      ∑ i ∈ t, c i • (P.bufferedCylinder N (A i)).indicator 1 := by
    funext omega
    have h := congrFun hexp (P.bufferedRestrict N omega)
    simpa only [PeriodicGraph.bufferedCylinder, Set.indicator_apply,
      Set.mem_preimage, Finset.sum_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul] using h
  calc
    (mu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) =
        ∫ omega, (P.bufferedCylinder N S).indicator (fun _ => (1 : ℝ)) omega ∂mu := by
          rw [integral_indicator_const (1 : ℝ)
            (P.bufferedCylinder_measurableSet N S)]
          simp
    _ = ∫ omega, (∑ i ∈ t,
          c i • (P.bufferedCylinder N (A i)).indicator
            (1 : ConfigSpace (Sym2 V) → ℝ)) omega ∂mu := by
          apply integral_congr_ae
          filter_upwards with omega
          simpa using congrFun hpoint omega
    _ = ∑ i ∈ t, c i *
          (mu : Measure (ConfigSpace (Sym2 V))).real
            (P.bufferedCylinder N (A i)) := by
          simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro i hi
            rw [integral_const_mul]
            congr 1
            simpa using (integral_indicator_const (μ := (mu : Measure _)) (1 : ℝ)
              (P.bufferedCylinder_measurableSet N (A i)))
          · intro i hi
            exact ((integrable_const (1 : ℝ)).indicator
              (P.bufferedCylinder_measurableSet N (A i))).const_mul _

theorem PeriodicGraph.freeBuffered_subseq_allCylinder_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.freeBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
    (N : ℕ) (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    (nu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) =
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
  classical
  have hdep : DependsOn
      (S.indicator (1 : ConfigSpace (Sym2 (P.BufferedVertex N)) → ℝ))
      (Finset.univ : Finset (Sym2 (P.BufferedVertex N))) := by
    intro omega eta heq
    congr 1
    funext e
    exact heq e (by simp)
  have hsigned := indicator_signedIncreasingCombo_of_dependsOn S Finset.univ hdep
  obtain ⟨I, t, c, A, hA, hexp⟩ :=
    (signedIncreasingCombo_iff
      (S.indicator (1 : ConfigSpace (Sym2 (P.BufferedVertex N)) → ℝ))).mp hsigned
  rw [P.bufferedCylinder_real_eq_signedSum nu N S t c A hexp,
    P.bufferedCylinder_real_eq_signedSum
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)) N S t c A hexp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [P.freeBuffered_subseq_cylinder_eq hp hp1 hq nu phi hphi hconv N (hA i hi)]

theorem PeriodicGraph.wiredBuffered_subseq_allCylinder_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.wiredBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
    (N : ℕ) (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    (nu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) =
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
  classical
  have hdep : DependsOn
      (S.indicator (1 : ConfigSpace (Sym2 (P.BufferedVertex N)) → ℝ))
      (Finset.univ : Finset (Sym2 (P.BufferedVertex N))) := by
    intro omega eta heq
    congr 1
    funext e
    exact heq e (by simp)
  have hsigned := indicator_signedIncreasingCombo_of_dependsOn S Finset.univ hdep
  obtain ⟨I, t, c, A, hA, hexp⟩ :=
    (signedIncreasingCombo_iff
      (S.indicator (1 : ConfigSpace (Sym2 (P.BufferedVertex N)) → ℝ))).mp hsigned
  rw [P.bufferedCylinder_real_eq_signedSum nu N S t c A hexp,
    P.bufferedCylinder_real_eq_signedSum
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)) N S t c A hexp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [P.wiredBuffered_subseq_cylinder_eq hp hp1 hq nu phi hphi hconv N (hA i hi)]

omit [Countable V] in


theorem PeriodicGraph.fullCylinder_eq_bufferedCylinder
    (P : PeriodicGraph V) (N : ℕ) (s : Finset (Sym2 V))
    (S : Set (∀ _i : s, Bool))
    (hs : ∀ e ∈ s, e ∈ Set.range (P.edgeIncl (P.bufferedRadius N))) :
    cylinder s S = P.bufferedCylinder N
      (P.extendEdge (P.bufferedRadius N) ⁻¹' cylinder s S) := by
  ext omega
  simp only [PeriodicGraph.bufferedCylinder, Set.mem_preimage]
  have hrestr : s.restrict
      (P.extendEdge (P.bufferedRadius N) (P.bufferedRestrict N omega)) =
      s.restrict omega := by
    funext e
    obtain ⟨eb, heb⟩ := hs e.1 e.2
    change P.extendEdge (P.bufferedRadius N) (P.bufferedRestrict N omega) e.1 = omega e.1
    rw [← heb, P.extendEdge_edgeIncl]
    rfl
  simp only [mem_cylinder, hrestr]

theorem PeriodicGraph.freeBuffered_subseq_finiteCylinder_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.freeBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
    (s : Finset (Sym2 V)) (S : Set (∀ _i : s, Bool)) :
    (nu : Measure (ConfigSpace (Sym2 V))).real (cylinder s S) =
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (cylinder s S) := by
  obtain ⟨N, hs⟩ := P.exists_bufferedLevel_edges s
  rw [P.fullCylinder_eq_bufferedCylinder N s S hs]
  exact P.freeBuffered_subseq_allCylinder_eq hp hp1 hq nu phi hphi hconv N _

theorem PeriodicGraph.wiredBuffered_subseq_finiteCylinder_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.wiredBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
    (s : Finset (Sym2 V)) (S : Set (∀ _i : s, Bool)) :
    (nu : Measure (ConfigSpace (Sym2 V))).real (cylinder s S) =
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (cylinder s S) := by
  obtain ⟨N, hs⟩ := P.exists_bufferedLevel_edges s
  rw [P.fullCylinder_eq_bufferedCylinder N s S hs]
  exact P.wiredBuffered_subseq_allCylinder_eq hp hp1 hq nu phi hphi hconv N _

theorem probabilityMeasure_eq_of_finiteCylinder_real_eq
    {E : Type*} [Countable E]
    (mu nu : ProbabilityMeasure (ConfigSpace E))
    (h : ∀ (s : Finset E) (S : Set (∀ _i : s, Bool)),
      (mu : Measure (ConfigSpace E)).real (cylinder s S) =
        (nu : Measure (ConfigSpace E)).real (cylinder s S)) :
    mu = nu := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_generate_finite (measurableCylinders (fun _ : E => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro C hC
    rw [mem_measurableCylinders] at hC
    obtain ⟨s, S, hS, rfl⟩ := hC
    have hreal := h s S
    unfold Measure.real at hreal
    exact (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top (mu : Measure (ConfigSpace E)) (cylinder s S))
      (measure_ne_top (nu : Measure (ConfigSpace E)) (cylinder s S))).mp hreal
  · rw [measure_univ, measure_univ]


theorem PeriodicGraph.freeBuffered_subseq_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.freeBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu) :
    nu = P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) := by
  apply probabilityMeasure_eq_of_finiteCylinder_real_eq
  exact P.freeBuffered_subseq_finiteCylinder_eq hp hp1 hq nu phi hphi hconv


theorem PeriodicGraph.wiredBuffered_subseq_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.wiredBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu) :
    nu = P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) := by
  apply probabilityMeasure_eq_of_finiteCylinder_real_eq
  exact P.wiredBuffered_subseq_finiteCylinder_eq hp hp1 hq nu phi hphi hconv


theorem PeriodicGraph.freeBufferedMeasure_weakConverges
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    WeakConvergesTo
      (fun n => P.freeBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq))
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)) := by
  rw [WeakConvergesTo]
  apply tendsto_nhds_of_unique_mapClusterPt
  intro nu hnu
  obtain ⟨phi, hphi, hconv⟩ := hnu.tendsto_subseq
  apply P.freeBuffered_subseq_eq hp hp1 hq nu phi hphi
  simpa [Function.comp_def] using hconv


theorem PeriodicGraph.wiredBufferedMeasure_weakConverges
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    WeakConvergesTo
      (fun n => P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq))
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)) := by
  rw [WeakConvergesTo]
  apply tendsto_nhds_of_unique_mapClusterPt
  intro nu hnu
  obtain ⟨phi, hphi, hconv⟩ := hnu.tendsto_subseq
  apply P.wiredBuffered_subseq_eq hp hp1 hq nu phi hphi
  simpa [Function.comp_def] using hconv


theorem PeriodicGraph.freeBufferedMeasure_tendsto_finiteCylinder
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (s : Finset (Sym2 V)) (S : Set (∀ _i : s, Bool)) :
    Tendsto
      (fun n => (P.freeBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (cylinder s S)) atTop
      (nhds ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (cylinder s S))) :=
  (P.freeBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
    (isClopen_cylinderEvent s S)


theorem PeriodicGraph.wiredBufferedMeasure_tendsto_finiteCylinder
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (s : Finset (Sym2 V)) (S : Set (∀ _i : s, Bool)) :
    Tendsto
      (fun n => (P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (cylinder s S)) atTop
      (nhds ((P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (cylinder s S))) :=
  (P.wiredBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
    (isClopen_cylinderEvent s S)

end PeriodicPlanar
end FK
end StatMech
