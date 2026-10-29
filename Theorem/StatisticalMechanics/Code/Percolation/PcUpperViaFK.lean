/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperPeierls
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
import Theorem.StatisticalMechanics.Code.FK.Ergodicity
import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Theorem.StatisticalMechanics.Code.Probability.InfiniteBK
open MeasureTheory Filter Topology Set Finset
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace FK

open StatMech.Lattice


theorem bernoulliProduct_map_injective_restrict
    {I E : Type*} [Countable I] [Countable E]
    (p : NNReal) (hp : p ≤ 1) (f : I → E) (hf : Function.Injective f) :
    Measure.map (fun (omega : ConfigSpace E) (i : I) => omega (f i))
        (bernoulliProductMeasure (E := E) p hp) =
      bernoulliProductMeasure (E := I) p hp := by
  have hind : ProbabilityTheory.iIndepFun
      (fun (i : I) (omega : ConfigSpace E) => omega (f i))
      (bernoulliProductMeasure (E := E) p hp) :=
    ProbabilityTheory.iIndepFun.precomp hf (bernoulli_iIndepFun p hp)
  have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i => measurable_pi_apply (f i))).mp hind
  rw [hmap]
  have hmarg : ∀ i : I,
      Measure.map (fun (omega : ConfigSpace E) => omega (f i))
          (bernoulliProductMeasure (E := E) p hp) = bernoulliMeasure p hp := by
    intro i
    unfold bernoulliProductMeasure
    exact Measure.infinitePi_map_eval (fun _ : E => bernoulliMeasure p hp) (f i)
  simp_rw [hmarg]
  unfold bernoulliProductMeasure
  rfl

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fkProbOne_pattern (p : ℝ) (eta : ConfigSpace ↥G.edgeFinset) :
    ∑ omega : ConfigSpace (Sym2 V),
        (if G.edgeFinset.restrict omega = eta then (1 : ℝ) else 0) *
          fkProb G p 1 omega = configWeight p eta := by
  classical
  let F := G.edgeFinset
  change ConfigSpace ↥F at eta
  let w : Sym2 V → Bool → ℝ := fun e b =>
    if he : e ∈ F then
      if b = eta ⟨e, he⟩ then (if b then p else 1 - p) else 0
    else 1
  have hnum :
      (∑ omega : ConfigSpace (Sym2 V),
          (if F.restrict omega = eta then (1 : ℝ) else 0) * edgeProduct G p omega) =
        2 ^ (Fintype.card (Sym2 V) - F.card) * configWeight p eta := by
    have hpoint : ∀ omega : ConfigSpace (Sym2 V),
        (if F.restrict omega = eta then (1 : ℝ) else 0) * edgeProduct G p omega =
          ∏ e ∈ F, w e (omega e) := by
      intro omega
      by_cases hrest : F.restrict omega = eta
      · rw [if_pos hrest, one_mul]
        unfold edgeProduct
        apply Finset.prod_congr rfl
        intro e he
        change e ∈ F at he
        have hev : omega e = eta ⟨e, he⟩ := by
          have := congrFun hrest ⟨e, he⟩
          simpa [Finset.restrict] using this
        simp only [w, he, dite_true, hev, if_pos]
      · rw [if_neg hrest, zero_mul]
        have hex : ∃ e : ↥F, omega e ≠ eta e := by
          by_contra h
          simp only [not_exists, not_not] at h
          apply hrest
          funext e
          exact h e
        obtain ⟨e, he⟩ := hex
        symm
        apply Finset.prod_eq_zero (i := (e : Sym2 V)) e.2
        have hene : omega (e : Sym2 V) ≠ eta ⟨(e : Sym2 V), e.2⟩ := by
          simpa using he
        simp only [w, e.2, dite_true, hene, if_false]
    calc
      (∑ omega : ConfigSpace (Sym2 V),
          (if F.restrict omega = eta then (1 : ℝ) else 0) * edgeProduct G p omega) =
          ∑ omega : ConfigSpace (Sym2 V), ∏ e ∈ F, w e (omega e) := by
            apply Finset.sum_congr rfl
            intro omega _
            exact hpoint omega
      _ = 2 ^ (Fintype.card (Sym2 V) - F.card) *
          ∏ e ∈ F, (∑ b : Bool, w e b) := sum_prod_factor F w
      _ = 2 ^ (Fintype.card (Sym2 V) - F.card) * configWeight p eta := by
        congr 1
        unfold configWeight edgeWeight
        rw [← Finset.prod_attach]
        apply Finset.prod_congr rfl
        intro e _
        have heF : (e : Sym2 V) ∈ F := e.2
        simp only [w, heF, dite_true]
        cases eta e <;> simp
  have hZ : fkZ G p 1 = 2 ^ (Fintype.card (Sym2 V) - F.card) := by
    rw [fkZ_one]
    change (∑ omega : ConfigSpace (Sym2 V),
      ∏ e ∈ F, (fun _ b => if b then p else 1 - p) e (omega e)) = _
    rw [sum_prod_factor F (fun _ b => if b then p else 1 - p)]
    simp
  have hpow : (0 : ℝ) < 2 ^ (Fintype.card (Sym2 V) - F.card) := by positivity
  simpa only [F] using (show
    (∑ omega : ConfigSpace (Sym2 V),
        (if G.edgeFinset.restrict omega = eta then (1 : ℝ) else 0) *
          fkProb G p 1 omega) = configWeight p eta from by
   calc
    (∑ omega : ConfigSpace (Sym2 V),
        (if G.edgeFinset.restrict omega = eta then (1 : ℝ) else 0) *
          fkProb G p 1 omega) =
        (∑ omega : ConfigSpace (Sym2 V),
          (if F.restrict omega = eta then (1 : ℝ) else 0) * edgeProduct G p omega) /
            fkZ G p 1 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro omega _
      unfold fkProb
      rw [fkWeight_one]
      ring
    _ = (2 ^ (Fintype.card (Sym2 V) - F.card) * configWeight p eta) /
          2 ^ (Fintype.card (Sym2 V) - F.card) := by rw [hnum, hZ]
    _ = configWeight p eta := by field_simp)


theorem fkProbOne_event_eq_bernoulli {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace (Sym2 V)))
    (hA : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ)))
      (G.edgeFinset : Set (Sym2 V))) :
    ∑ omega : ConfigSpace (Sym2 V),
        A.indicator (fun _ => (1 : ℝ)) omega * fkProb G p 1 omega =
      (bernoulliProductMeasure (E := Sym2 V) ⟨p, hp.le⟩
        (by exact_mod_cast hp1.le)).real A := by
  classical
  let F := G.edgeFinset
  let B : Set (ConfigSpace ↥F) := F.restrict '' A
  have hmem : ∀ omega : ConfigSpace (Sym2 V),
      omega ∈ A ↔ F.restrict omega ∈ B := by
    intro omega
    rw [show A = cylinder F B from eq_cylinder_restrict_image A F hA]
    rfl
  rw [realProb_cylinder_eq_finsum ⟨p, hp.le⟩ (by exact_mod_cast hp1.le) A F hA]
  calc
    (∑ omega : ConfigSpace (Sym2 V),
        A.indicator (fun _ => (1 : ℝ)) omega * fkProb G p 1 omega) =
      ∑ omega : ConfigSpace (Sym2 V),
        ∑ eta : ConfigSpace ↥F,
          B.indicator (fun _ => (1 : ℝ)) eta *
            ((if F.restrict omega = eta then (1 : ℝ) else 0) * fkProb G p 1 omega) := by
      apply Finset.sum_congr rfl
      intro omega _
      by_cases hω : omega ∈ A
      · rw [Set.indicator_of_mem hω]
        have hr : F.restrict omega ∈ B := (hmem omega).1 hω
        simp only [Set.indicator_apply]
        simp [hr]
      · rw [Set.indicator_of_notMem hω]
        have hr : F.restrict omega ∉ B := fun h => hω ((hmem omega).2 h)
        simp only [Set.indicator_apply]
        simp [hr]
    _ = ∑ eta : ConfigSpace ↥F,
        B.indicator (fun _ => (1 : ℝ)) eta *
          ∑ omega : ConfigSpace (Sym2 V),
            (if F.restrict omega = eta then (1 : ℝ) else 0) * fkProb G p 1 omega := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro eta _
      rw [Finset.mul_sum]
    _ = ∑ eta : ConfigSpace ↥F,
        B.indicator (fun _ => (1 : ℝ)) eta * configWeight p eta := by
      apply Finset.sum_congr rfl
      intro eta _
      rw [fkProbOne_pattern G p eta]
    _ = ∑ eta : ConfigSpace ↥F,
        (F.restrict '' A).indicator (fun _ => (1 : ℝ)) eta *
          ∏ e : ↥F, (if eta e then p else 1 - p) := by
      rfl


theorem connToBdryEvent_dependsOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V → Prop) (x : V) :
    _root_.DependsOn
      ({omega : ConfigSpace (Sym2 V) |
        IsingFK.ConnToBdry G bdry omega x}.indicator (fun _ => (1 : ℝ)))
      (G.edgeFinset : Set (Sym2 V)) := by
  classical
  intro omega omega' heq
  have hopen : openSub G omega = openSub G omega' := by
    ext u v
    simp only [openSub_adj]
    constructor
    · rintro ⟨huv, hopen⟩
      refine ⟨huv, ?_⟩
      rw [← heq s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv)]
      exact hopen
    · rintro ⟨huv, hopen⟩
      refine ⟨huv, ?_⟩
      rw [heq s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv)]
      exact hopen
  have hiff : IsingFK.ConnToBdry G bdry omega x ↔
      IsingFK.ConnToBdry G bdry omega' x := by
    unfold IsingFK.ConnToBdry Connected
    rw [hopen]
  by_cases h : IsingFK.ConnToBdry G bdry omega x
  · have hm : omega ∈ {omega | IsingFK.ConnToBdry G bdry omega x} := h
    have hm' : omega' ∈ {omega | IsingFK.ConnToBdry G bdry omega x} := hiff.mp h
    rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm']
  · have hm : omega ∉ {omega | IsingFK.ConnToBdry G bdry omega x} := h
    have hm' : omega' ∉ {omega | IsingFK.ConnToBdry G bdry omega x} :=
      fun h' => h (hiff.mpr h')
    rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm']


variable {d : ℕ}


theorem bernoulliProduct_map_boxRestrict (p : NNReal) (hp : p ≤ 1) (n : ℕ) :
    Measure.map (boxRestrict d n)
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) =
      bernoulliProductMeasure (E := Sym2 (boxVerts d n)) p hp := by
  simpa only [boxRestrict] using
    (bernoulliProduct_map_injective_restrict p hp (edgeIncl d n)
      (edgeIncl_injective d n))


theorem bernoulliProduct_boxRestrict_preimage (p : NNReal) (hp : p ≤ 1)
    (n : ℕ) (A : Set (ConfigSpace (Sym2 (boxVerts d n)))) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (boxRestrict d n ⁻¹' A) =
      (bernoulliProductMeasure (E := Sym2 (boxVerts d n)) p hp).real A := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site d)) p hp
  let nu := bernoulliProductMeasure (E := Sym2 (boxVerts d n)) p hp
  have hpres : MeasurePreserving (boxRestrict d n) mu nu :=
    ⟨(continuous_boxRestrict d n).measurable,
      bernoulliProduct_map_boxRestrict p hp n⟩
  exact hpres.measureReal_preimage MeasurableSet.of_discrete.nullMeasurableSet


theorem wiredFinite_boxBdryConnEvent_le_bernoulli
    (p : NNReal) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    (wiredFiniteMeasure d n (by exact_mod_cast hp0) (by exact_mod_cast hp1)
        (by norm_num : (0 : ℝ) < 2) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) ≤
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1.le).real
        (boxBdryConnEvent d n) := by
  let A : Set (ConfigSpace (Sym2 (boxVerts d n))) :=
    {omega | IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega
      (IsingFK.boxOrigin d n)}
  have hAinc : IsIncreasing A := isIncreasing_connToBdryEvent n
  have hAdep : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ)))
      ((boxGraph d n).edgeFinset : Set (Sym2 (boxVerts d n))) :=
    connToBdryEvent_dependsOn (boxGraph d n) (boxBoundary d n)
      (IsingFK.boxOrigin d n)
  have hHolley := wiredFkProb_le_fkProbOne_increasing
    (boxGraph d n) (boxBoundary d n) (by exact_mod_cast hp0)
      (by exact_mod_cast hp1) (by norm_num : (1 : ℝ) ≤ 2) hAinc
  have hfinite :
      (∑ omega : ConfigSpace (Sym2 (boxVerts d n)),
        A.indicator (fun _ => (1 : ℝ)) omega *
          wiredFkProb (boxGraph d n) (boxBoundary d n) (p : ℝ) 2 omega) ≤
      (bernoulliProductMeasure (E := Sym2 (boxVerts d n)) p hp1.le).real A := by
    exact hHolley.trans_eq
      (fkProbOne_event_eq_bernoulli (boxGraph d n)
        (by exact_mod_cast hp0) (by exact_mod_cast hp1) A hAdep)
  rw [show boxBdryConnEvent d n = boxRestrict d n ⁻¹' A from rfl,
    wiredFiniteMeasure_real_boxRestrictEvent n (by exact_mod_cast hp0)
      (by exact_mod_cast hp1) A
      ((continuous_boxRestrict d n).measurable MeasurableSet.of_discrete),
    bernoulliProduct_boxRestrict_preimage]
  exact hfinite


theorem fkTheta_two_le_bernoulliTheta
    (p : NNReal) (hp0 : 0 < p) (hp1 : p < 1) :
    fkTheta d (by exact_mod_cast hp0) (by exact_mod_cast hp1)
        (by norm_num : (0 : ℝ) < 2) (q := 2) ≤
      Percolation.theta d p hp1.le := by
  have hfk := boxBdryConnEvent_diag_tendsto (d := d)
    (by exact_mod_cast hp0) (by exact_mod_cast hp1)
  have hbern := boxBdryConnEvent_real_tendsto_percolation (d := d)
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1.le)
  apply le_of_tendsto_of_tendsto hfk
    (by simpa only [Percolation.theta] using hbern)
  exact Filter.Eventually.of_forall
    (wiredFinite_boxBdryConnEvent_le_bernoulli p hp0 hp1)

end FK
end StatMech
