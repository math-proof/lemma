/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.FK.Comparison
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Def.StatisticalMechanics.Code.FK.PcNontrivial
open MeasureTheory Filter Topology Set SimpleGraph
open scoped NNReal ENNReal BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


variable {d : ℕ}


theorem isClopen_singleOpen (e : Sym2 (Site d)) :
    IsClopen {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} := by
  have h : {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} = (fun ω => ω e) ⁻¹' {true} := rfl
  rw [h]
  exact IsClopen.preimage (isClopen_discrete _) (StatMech.ConfigSpace.continuous_eval e)


theorem isClopen_wordEvent (g : ℕ → Fin d × Bool) (m : ℕ) : IsClopen (wordEvent g m) := by
  have heq : wordEvent g m
      = ⋂ k ∈ (Finset.range m : Set ℕ),
          {ω : ConfigSpace (Sym2 (Site d)) | ω (edgeOf g k) = true} := by
    ext ω
    simp only [wordEvent, Set.mem_setOf_eq, Set.mem_iInter, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro h k hk; exact h k (Finset.mem_range.mpr hk)
    · intro h k hk; exact h k (Finset.mem_range.mp hk)
  rw [heq]
  exact Set.Finite.isClopen_biInter (Finset.finite_toSet _) (fun k _ => isClopen_singleOpen _)


theorem isIncreasing_wordEvent (g : ℕ → Fin d × Bool) (m : ℕ) : IsIncreasing (wordEvent g m) := by
  intro x y hxy hx k hk
  have := hxy (edgeOf g k)
  rw [hx k hk] at this
  exact le_antisymm le_top this


theorem isClopen_fkExistsOpenWalk (m : ℕ) (hd : 0 < d) : IsClopen (fkExistsOpenWalk d m hd) := by
  rw [fkExistsOpenWalk]
  apply isClopen_iUnion_of_finite
  intro w
  by_cases hgw : goodWord (fkExtWord m hd w) m
  · rw [Set.iUnion_eq_if, if_pos hgw]; exact isClopen_wordEvent _ _
  · rw [Set.iUnion_eq_if, if_neg hgw]; exact isClopen_empty


theorem isIncreasing_fkExistsOpenWalk (m : ℕ) (hd : 0 < d) :
    IsIncreasing (fkExistsOpenWalk d m hd) := by
  apply isUpperSet_iUnion₂
  intro w _
  exact isIncreasing_wordEvent _ _


theorem percolationEvent_subset_fkExistsOpenWalk (hd : 0 < d) (m : ℕ) :
    percolationEvent d ⊆ fkExistsOpenWalk d m hd := by
  refine (percolationEvent_subset_iUnion_wordEvent hd m).trans ?_
  refine Set.iUnion_subset (fun g => Set.iUnion_subset (fun hg => ?_))
  set w : Fin m → Fin d × Bool := fun i => g i.1 with hw
  have hvert : ∀ j ≤ m, vertOf g j = vertOf (fkExtWord m hd w) j := by
    intro j hj
    induction j with
    | zero => rfl
    | succ k ih =>
      have hk : k < m := by omega
      rw [vertOf_succ, vertOf_succ, ih (by omega)]
      congr 1 <;> simp only [fkExtWord, dif_pos hk, hw]
  have hgood' : goodWord (fkExtWord m hd w) m := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rw [← hvert a (by omega), ← hvert b (by omega)] at hab
    exact hg (by simp only [Finset.coe_range, Set.mem_Iio]; omega)
      (by simp only [Finset.coe_range, Set.mem_Iio]; omega) hab
  have hwe : wordEvent g m = wordEvent (fkExtWord m hd w) m := by
    apply Set.ext; intro ω
    simp only [wordEvent, Set.mem_setOf_eq, Finset.mem_range]
    have hedge : ∀ k < m, edgeOf g k = edgeOf (fkExtWord m hd w) k := by
      intro k hk; unfold edgeOf; rw [hvert k (by omega), hvert (k + 1) (by omega)]
    constructor
    · intro h k hk; rw [← hedge k hk]; exact h k hk
    · intro h k hk; rw [hedge k hk]; exact h k hk
  rw [hwe]
  exact Set.subset_iUnion_of_subset w (Set.subset_iUnion_of_subset hgood' (le_refl _))


theorem extendEdge_eq_of_range (n : ℕ) (be : Sym2 (boxVerts d n))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    extendEdge d n ω (edgeIncl d n be) = ω be := by
  unfold extendEdge
  have hmem : edgeIncl d n be ∈ Set.range (edgeIncl d n) := ⟨be, rfl⟩
  rw [dif_pos hmem, edgeIncl_injective d n hmem.choose_spec]


theorem range_of_extendEdge_true (n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (e : Sym2 (Site d)) (h : extendEdge d n ω e = true) : e ∈ Set.range (edgeIncl d n) := by
  by_contra hc; unfold extendEdge at h; rw [dif_neg hc] at h; exact absurd h (by simp)


theorem boxEdge_mem (n : ℕ) (be : Sym2 (boxVerts d n)) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) (heq : edgeIncl d n be = s(x, y)) :
    be ∈ (boxGraph d n).edgeFinset := by
  induction be using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj]
    unfold edgeIncl at heq
    rw [Sym2.map_mk, Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · show (hypercubicLattice d).Adj (u : Site d) (v : Site d); rw [h1, h2]; exact hadj
    · show (hypercubicLattice d).Adj (u : Site d) (v : Site d); rw [h1, h2]; exact hadj.symm


theorem exists_boxF (n m : ℕ) (g : ℕ → Fin d × Bool) (hg : goodWord g m)
    (hrange : ∀ k ∈ Finset.range m, edgeOf g k ∈ Set.range (edgeIncl d n)) :
    ∃ F : Finset (Sym2 (boxVerts d n)), F ⊆ (boxGraph d n).edgeFinset ∧ F.card = m ∧
      (extendEdge d n ⁻¹' wordEvent g m ⊆ {ω | ∀ be ∈ F, ω be = true}) := by
  classical
  set bef : {k // k ∈ Finset.range m} → Sym2 (boxVerts d n) :=
    fun k => (hrange k.1 k.2).choose with hbef
  have hbef_spec : ∀ k : {k // k ∈ Finset.range m}, edgeIncl d n (bef k) = edgeOf g k.1 :=
    fun k => (hrange k.1 k.2).choose_spec
  refine ⟨(Finset.range m).attach.image bef, ?_, ?_, ?_⟩
  · intro f hf
    simp only [Finset.mem_image, Finset.mem_attach, true_and] at hf
    obtain ⟨k, rfl⟩ := hf
    have hadj : (hypercubicLattice d).Adj (vertOf g k.1) (vertOf g (k.1 + 1)) := by
      rw [vertOf_succ]; exact adj_coordShift _ _ _
    exact boxEdge_mem n (bef k) _ _ hadj (by rw [hbef_spec k]; rfl)
  · rw [Finset.card_image_of_injOn, Finset.card_attach, Finset.card_range]
    intro a _ b _ hab
    have heq : edgeIncl d n (bef a) = edgeIncl d n (bef b) := by rw [hab]
    rw [hbef_spec a, hbef_spec b] at heq
    have ha := Finset.mem_range.mp a.2
    have hb := Finset.mem_range.mp b.2
    exact Subtype.ext ((edgeOf_injOn g m hg) (by simp [ha]) (by simp [hb]) heq)
  · intro ω hω be hbe
    simp only [Finset.mem_image, Finset.mem_attach, true_and] at hbe
    obtain ⟨k, rfl⟩ := hbe
    simp only [Set.mem_preimage, wordEvent, Set.mem_setOf_eq] at hω
    have htrue := hω k.1 k.2
    rw [← hbef_spec k] at htrue
    rw [extendEdge_eq_of_range] at htrue
    exact htrue


theorem perWord_box_bound (n m : ℕ) (g : ℕ → Fin d × Bool) (hg : goodWord g m)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
        (extendEdge d n ⁻¹' wordEvent g m).indicator (fun _ => (1 : ℝ)) ω
          * fkProb (boxGraph d n) p 1 ω ≤ p ^ m := by
  classical
  by_cases hempty : (extendEdge d n ⁻¹' wordEvent g m) = ∅
  · rw [hempty]
    simp only [Set.indicator_empty, zero_mul, Finset.sum_const_zero]
    positivity
  · rw [← Set.not_nonempty_iff_eq_empty, not_not] at hempty
    obtain ⟨ω0, hω0⟩ := hempty
    simp only [Set.mem_preimage, wordEvent, Set.mem_setOf_eq] at hω0
    have hrange : ∀ k ∈ Finset.range m, edgeOf g k ∈ Set.range (edgeIncl d n) :=
      fun k hk => range_of_extendEdge_true n ω0 _ (hω0 k hk)
    obtain ⟨F, hFsub, hFcard, hFcont⟩ := exists_boxF n m g hg hrange
    calc ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
            (extendEdge d n ⁻¹' wordEvent g m).indicator (fun _ => (1 : ℝ)) ω
              * fkProb (boxGraph d n) p 1 ω
        ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
            (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * fkProb (boxGraph d n) p 1 ω := by
          apply Finset.sum_le_sum
          intro ω _
          apply mul_le_mul_of_nonneg_right _ (fkProb_nonneg (boxGraph d n) hp hp1 one_pos ω)
          by_cases hω : ω ∈ extendEdge d n ⁻¹' wordEvent g m
          · rw [Set.indicator_of_mem hω]
            have hmem : ∀ be ∈ F, ω be = true := hFcont hω
            rw [if_pos hmem]
          · rw [Set.indicator_of_notMem hω]; split <;> positivity
      _ = p ^ F.card := fkProbOne_cylinder (boxGraph d n) hp hp1 F hFsub
      _ = p ^ m := by rw [hFcard]


theorem wiredFiniteMeasure_real_eq (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 (Site d)))) (hA : MeasurableSet A) :
    (wiredFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real A
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (extendEdge d n ⁻¹' A).indicator (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  have hw : (wiredFiniteMeasure d n hp hp1 hq : Measure _).real A
      = ((wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq).toMeasure
          (extendEdge d n ⁻¹' A)).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d n) hA]
  rw [hw, wiredFkPMF_toMeasure_toReal]


theorem wiredFiniteMeasure_fkExistsOpenWalk_le (n m : ℕ) (hd : 0 < d) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fkExistsOpenWalk d m hd)
      ≤ ((2 * d : ℝ) * p) ^ m := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hAmeas : MeasurableSet (fkExistsOpenWalk d m hd) :=
    IsClopen.measurableSet_configSpace (isClopen_fkExistsOpenWalk m hd)
  
  set μ1 := fkProb (boxGraph d n) p 1 with hμ1
  
  rw [wiredFiniteMeasure_real_eq n hp hp1 hq0 _ hAmeas]
  
  have hHolley :
      (∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (extendEdge d n ⁻¹' fkExistsOpenWalk d m hd).indicator (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω)
        ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
            (extendEdge d n ⁻¹' fkExistsOpenWalk d m hd).indicator (fun _ => (1 : ℝ)) ω
              * fkProb (boxGraph d n) p 1 ω :=
    wiredFkProb_le_fkProbOne_increasing (boxGraph d n) (boxBoundary d n) hp hp1 hq
      (isIncreasing_preimage_extendEdge d n (isIncreasing_fkExistsOpenWalk m hd))
  refine hHolley.trans ?_
  
  set S : Finset (Fin m → Fin d × Bool) :=
    Finset.univ.filter (fun w => goodWord (fkExtWord m hd w) m) with hS
  
  have hsplit : ∀ ω : ConfigSpace (Sym2 (boxVerts d n)),
      (extendEdge d n ⁻¹' fkExistsOpenWalk d m hd).indicator (fun _ => (1 : ℝ)) ω
        ≤ ∑ w ∈ S, (extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ extendEdge d n ⁻¹' fkExistsOpenWalk d m hd
    · rw [Set.indicator_of_mem hω]
      rw [Set.mem_preimage, fkExistsOpenWalk, Set.mem_iUnion₂] at hω
      obtain ⟨w, hgw, hwe⟩ := hω
      have hmem : w ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgw⟩
      have hωmem : ω ∈ extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m := hwe
      have hstep := Finset.single_le_sum
        (f := fun w => (extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m).indicator (fun _ => (1 : ℝ)) ω)
        (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω) hmem
      simp only [] at hstep
      rwa [Set.indicator_of_mem hωmem] at hstep
    · rw [Set.indicator_of_notMem hω]
      exact Finset.sum_nonneg (fun w _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  
  calc ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (extendEdge d n ⁻¹' fkExistsOpenWalk d m hd).indicator (fun _ => (1 : ℝ)) ω * μ1 ω
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (∑ w ∈ S, (extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m).indicator (fun _ => (1 : ℝ)) ω)
            * μ1 ω := by
        apply Finset.sum_le_sum
        intro ω _
        exact mul_le_mul_of_nonneg_right (hsplit ω) (fkProb_nonneg (boxGraph d n) hp hp1 one_pos ω)
    _ = ∑ w ∈ S, ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m).indicator (fun _ => (1 : ℝ)) ω * μ1 ω := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun ω _ => ?_)
        rw [Finset.sum_mul]
    _ ≤ ∑ w ∈ S, p ^ m := by
        apply Finset.sum_le_sum
        intro w hw
        exact perWord_box_bound n m (fkExtWord m hd w) (Finset.mem_filter.mp hw).2 hp hp1
    _ = (S.card : ℝ) * p ^ m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Finset.univ : Finset (Fin m → Fin d × Bool)).card : ℝ) * p ^ m := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp.le m)
        exact_mod_cast Finset.card_le_card (Finset.subset_univ S)
    _ = ((2 * d : ℝ) * p) ^ m := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool, Fintype.card_fin]
        push_cast
        rw [mul_pow]
        ring_nf


theorem fkTheta_le_pow (hd : 0 < d) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (m : ℕ) :
    fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) ≤ ((2 * d : ℝ) * p) ^ m := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨φ, hφ, htends⟩ := wiredInfiniteVolume_isLimit d hp hp1 hq0
  
  have hmono : fkTheta d hp hp1 hq0 (q := q)
      ≤ (wiredInfiniteVolume d hp hp1 hq0 : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fkExistsOpenWalk d m hd) := by
    unfold fkTheta
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (percolationEvent_subset_fkExistsOpenWalk hd m))
  
  have hlim : (wiredInfiniteVolume d hp hp1 hq0 : Measure (ConfigSpace (Sym2 (Site d)))).real
        (fkExistsOpenWalk d m hd) ≤ ((2 * d : ℝ) * p) ^ m :=
    le_of_tendsto (htends.tendsto_real_of_isClopen (isClopen_fkExistsOpenWalk m hd))
      (Filter.Eventually.of_forall
        (fun n => wiredFiniteMeasure_fkExistsOpenWalk_le (φ n) m hd hp hp1 hq))
  exact hmono.trans hlim


theorem fkTheta_eq_zero_of_lt (hd : 0 < d) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hsmall : (2 * d : ℝ) * p < 1) :
    fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) = 0 := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hbase_nonneg : (0 : ℝ) ≤ (2 * d : ℝ) * p := by positivity
  have htend : Filter.Tendsto (fun m => ((2 * d : ℝ) * p) ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hsmall
  have hle : fkTheta d hp hp1 hq0 (q := q) ≤ 0 :=
    ge_of_tendsto htend (Filter.Eventually.of_forall (fun m => fkTheta_le_pow hd hp hp1 hq m))
  exact le_antisymm hle (fkTheta_nonneg d hp hp1 hq0 (q := q))


theorem fkSubcriticalSet_bddAbove (d : ℕ) (q : ℝ) : BddAbove (fkSubcriticalSet d q) := by
  refine ⟨1, fun x hx => ?_⟩
  obtain ⟨hp, hp1, hq, _⟩ := hx
  exact hp1.le


theorem le_fkPc_of_mem {d : ℕ} {q p : ℝ} (hp : p ∈ fkSubcriticalSet d q) : p ≤ fkPc d q :=
  le_csSup (fkSubcriticalSet_bddAbove d q) hp


theorem fkPc_pos (hd : 0 < d) {q : ℝ} (hq : 1 ≤ q) : 0 < fkPc d q := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  
  set p : ℝ := 1 / (4 * d) with hp_def
  have hp_pos : 0 < p := by rw [hp_def]; positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : p < 1 := by
    rw [hp_def, div_lt_one (by positivity)]; nlinarith
  have hsmall : (2 * d : ℝ) * p < 1 := by
    rw [hp_def, mul_one_div, div_lt_one (by positivity)]; nlinarith
  have hmem : p ∈ fkSubcriticalSet d q :=
    ⟨hp_pos, hp1, zero_lt_one.trans_le hq, fkTheta_eq_zero_of_lt hd hp_pos hp1 hq hsmall⟩
  exact lt_of_lt_of_le hp_pos (le_fkPc_of_mem hmem)


theorem fkPc_pos_of_two_le (hd : 2 ≤ d) {q : ℝ} (hq : 1 ≤ q) : 0 < fkPc d q :=
  fkPc_pos (by omega) hq

end FK
end StatMech
