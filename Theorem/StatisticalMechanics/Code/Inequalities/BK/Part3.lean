/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Inequalities.BK.Part3
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace


variable {E F : Type*}


lemma indicator_slice {n : ℕ} (S : Set (ConfigSpace (Fin (n + 1)))) (x : Bool)
    (ω' : ConfigSpace (Fin n)) :
    S.indicator (fun _ => (1 : ℝ)) (Fin.cons x ω')
      = (slice S x).indicator (fun _ => (1 : ℝ)) ω' := rfl


lemma pweight_cons {n : ℕ} (φ : Fin (n + 1) → Bool → ℝ) (x : Bool) (ω' : ConfigSpace (Fin n)) :
    pweight φ (Fin.cons x ω') = φ 0 x * pweight (fun j => φ j.succ) ω' := by
  simp only [pweight]
  rw [Fin.prod_univ_succ, Fin.cons_zero]
  exact congrArg _ (Finset.prod_congr rfl (fun j _ => by rw [Fin.cons_succ]))


theorem wprob_slice {n : ℕ} (φ : Fin (n + 1) → Bool → ℝ) (S : Set (ConfigSpace (Fin (n + 1)))) :
    wprob φ S = φ 0 false * wprob (fun j => φ j.succ) (slice S false)
             + φ 0 true * wprob (fun j => φ j.succ) (slice S true) := by
  have hx : ∀ x : Bool, ∑ ω' : ConfigSpace (Fin n),
      S.indicator (fun _ => (1 : ℝ)) (Fin.cons x ω') * pweight φ (Fin.cons x ω')
      = φ 0 x * wprob (fun j => φ j.succ) (slice S x) := by
    intro x
    simp only [wprob, indicator_slice, pweight_cons, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro ω' _; ring
  calc wprob φ S = ∑ ω, S.indicator (fun _ => (1 : ℝ)) ω * pweight φ ω := rfl
    _ = ∑ p : Bool × ConfigSpace (Fin n),
          S.indicator (fun _ => (1 : ℝ)) (Fin.cons p.1 p.2) * pweight φ (Fin.cons p.1 p.2) :=
          (Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool)) _ _ (fun p => rfl)).symm
    _ = ∑ x : Bool, ∑ ω' : ConfigSpace (Fin n),
          S.indicator (fun _ => (1 : ℝ)) (Fin.cons x ω') * pweight φ (Fin.cons x ω') :=
          Fintype.sum_prod_type _
    _ = φ 0 false * wprob (fun j => φ j.succ) (slice S false)
             + φ 0 true * wprob (fun j => φ j.succ) (slice S true) := by
          rw [Fintype.sum_bool, hx false, hx true]; ring


lemma slice_isIncreasing {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))} (hC : IsIncreasing C)
    (x : Bool) : IsIncreasing (slice C x) := by
  intro a b hab ha
  simp only [slice, Set.mem_setOf_eq] at ha ⊢
  apply hC _ ha
  intro i; refine Fin.cases ?_ ?_ i
  · simp [Fin.cons_zero]
  · intro j; simp only [Fin.cons_succ]; exact hab j


lemma slice_false_subset_true {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))}
    (hC : IsIncreasing C) : slice C false ⊆ slice C true := by
  intro ω' hω'
  simp only [slice, Set.mem_setOf_eq] at hω' ⊢
  apply hC _ hω'
  intro i; refine Fin.cases ?_ ?_ i
  · simp [Fin.cons_zero]
  · intro j; simp [Fin.cons_succ]


lemma occursOn_slice_of_false {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))}
    {K : Set (Fin (n + 1))} {ω' : ConfigSpace (Fin n)}
    (h : OccursOn C K (Fin.cons false ω')) :
    OccursOn (slice C false) (sliceSet K) ω' := by
  intro τ hτ
  simp only [slice, Set.mem_setOf_eq]
  apply h
  intro i hi; refine Fin.cases ?_ ?_ i hi
  · intro _; simp [Fin.cons_zero]
  · intro j hj; simp only [Fin.cons_succ]; exact hτ j hj


lemma occursOn_slice_true {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))}
    {K : Set (Fin (n + 1))} {ω' : ConfigSpace (Fin n)}
    (h : OccursOn C K (Fin.cons true ω')) :
    OccursOn (slice C true) (sliceSet K) ω' := by
  intro τ hτ
  simp only [slice, Set.mem_setOf_eq]
  apply h
  intro i hi; refine Fin.cases ?_ ?_ i hi
  · intro _; simp [Fin.cons_zero]
  · intro j hj; simp only [Fin.cons_succ]; exact hτ j hj


lemma occursOn_slice_false_notmem {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))}
    {K : Set (Fin (n + 1))} {x : Bool} {ω' : ConfigSpace (Fin n)}
    (h0 : (0 : Fin (n + 1)) ∉ K) (h : OccursOn C K (Fin.cons x ω')) :
    OccursOn (slice C false) (sliceSet K) ω' := by
  intro τ hτ
  simp only [slice, Set.mem_setOf_eq]
  apply h
  intro i hi; refine Fin.cases ?_ ?_ i hi
  · intro hi0; exact absurd hi0 h0
  · intro j hj; simp only [Fin.cons_succ]; exact hτ j hj


lemma sliceSet_disjoint {n : ℕ} {K L : Set (Fin (n + 1))} (h : Disjoint K L) :
    Disjoint (sliceSet K) (sliceSet L) := by
  rw [Set.disjoint_left] at h ⊢
  intro j hjK hjL
  exact h (a := j.succ) hjK hjL


theorem slice_disjointOccurrence_false {n : ℕ} {A B : Set (ConfigSpace (Fin (n + 1)))} :
    slice (disjointOccurrence A B) false ⊆
      disjointOccurrence (slice A false) (slice B false) := by
  intro ω' hω'
  simp only [slice, Set.mem_setOf_eq, mem_disjointOccurrence] at hω'
  obtain ⟨K, L, hKL, hA, hB⟩ := hω'
  exact ⟨sliceSet K, sliceSet L, sliceSet_disjoint hKL,
    occursOn_slice_of_false hA, occursOn_slice_of_false hB⟩


theorem slice_disjointOccurrence_true {n : ℕ} {A B : Set (ConfigSpace (Fin (n + 1)))} :
    slice (disjointOccurrence A B) true ⊆
      disjointOccurrence (slice A false) (slice B true) ∪
      disjointOccurrence (slice A true) (slice B false) := by
  intro ω' hω'
  simp only [slice, Set.mem_setOf_eq, mem_disjointOccurrence] at hω'
  obtain ⟨K, L, hKL, hA, hB⟩ := hω'
  by_cases h0K : (0 : Fin (n + 1)) ∈ K
  · have h0L : (0 : Fin (n + 1)) ∉ L := by rw [Set.disjoint_left] at hKL; exact hKL h0K
    right
    exact ⟨sliceSet K, sliceSet L, sliceSet_disjoint hKL,
      occursOn_slice_true hA, occursOn_slice_false_notmem h0L hB⟩
  · left
    exact ⟨sliceSet K, sliceSet L, sliceSet_disjoint hKL,
      occursOn_slice_false_notmem h0K hA, occursOn_slice_true hB⟩


lemma occursOn_subsingleton {n : ℕ} [Subsingleton (ConfigSpace (Fin n))]
    {A : Set (ConfigSpace (Fin n))} {K : Set (Fin n)} {ω : ConfigSpace (Fin n)} :
    OccursOn A K ω ↔ ω ∈ A := by
  refine ⟨OccursOn.mem_self, fun h ω' _ => ?_⟩
  rwa [Subsingleton.elim ω' ω]

lemma disjointOccurrence_subsingleton {n : ℕ} [Subsingleton (ConfigSpace (Fin n))]
    (A B : Set (ConfigSpace (Fin n))) :
    disjointOccurrence A B = A ∩ B := by
  ext ω
  rw [mem_disjointOccurrence]
  refine ⟨fun ⟨_, _, _, hA, hB⟩ => ⟨occursOn_subsingleton.mp hA, occursOn_subsingleton.mp hB⟩,
    fun ⟨hA, hB⟩ => ⟨∅, ∅, by simp, occursOn_subsingleton.mpr hA, occursOn_subsingleton.mpr hB⟩⟩


theorem bk_wprob : ∀ (n : ℕ) (φ : Fin n → Bool → ℝ),
    (∀ i b, 0 ≤ φ i b) → (∀ i, φ i false + φ i true = 1) →
    ∀ (A B : Set (ConfigSpace (Fin n))), IsIncreasing A → IsIncreasing B →
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  intro n
  induction n with
  | zero =>
    intro φ hφ0 _ A B _ _
    have hpw : pweight φ (default : ConfigSpace (Fin 0)) = 1 := by
      simp [pweight]
    have hval : ∀ S : Set (ConfigSpace (Fin 0)),
        wprob φ S = S.indicator (fun _ => (1 : ℝ)) (default : ConfigSpace (Fin 0)) := by
      intro S
      simp only [wprob]
      rw [Fintype.sum_subsingleton _ (default : ConfigSpace (Fin 0)), hpw, mul_one]
    rw [hval, hval, hval, disjointOccurrence_subsingleton]
    have hAB : (A ∩ B).indicator (fun _ => (1 : ℝ))
        = fun ω => A.indicator (fun _ => (1 : ℝ)) ω * B.indicator (fun _ => (1 : ℝ)) ω := by
      funext ω
      by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;>
        simp [Set.indicator, ha, hb, Set.mem_inter_iff]
    rw [hAB]
  | succ n ih =>
    intro φ hφ0 hφ1 A B hA hB
    set ψ : Fin n → Bool → ℝ := fun j => φ j.succ with hψ
    have hψ0 : ∀ i b, 0 ≤ ψ i b := fun i b => hφ0 i.succ b
    have hψ1 : ∀ i, ψ i false + ψ i true = 1 := fun i => hφ1 i.succ
    set q := φ 0 false with hqdef
    set p := φ 0 true with hpdef
    have hq0 : 0 ≤ q := hφ0 0 false
    have hp0 : 0 ≤ p := hφ0 0 true
    have hqp : q + p = 1 := hφ1 0
    have hqeq : q = 1 - p := by linarith
    set A0 := slice A false
    set A1 := slice A true
    set B0 := slice B false
    set B1 := slice B true
    have hA0 : IsIncreasing A0 := slice_isIncreasing hA false
    have hA1 : IsIncreasing A1 := slice_isIncreasing hA true
    have hB0 : IsIncreasing B0 := slice_isIncreasing hB false
    have hB1 : IsIncreasing B1 := slice_isIncreasing hB true
    have hA01 : A0 ⊆ A1 := slice_false_subset_true hA
    have hB01 : B0 ⊆ B1 := slice_false_subset_true hB
    set a0 := wprob ψ A0
    set a1 := wprob ψ A1
    set b0 := wprob ψ B0
    set b1 := wprob ψ B1
    have indA0B0 : wprob ψ (disjointOccurrence A0 B0) ≤ a0 * b0 := ih ψ hψ0 hψ1 A0 B0 hA0 hB0
    have indU : wprob ψ (disjointOccurrence A0 B1) ≤ a0 * b1 := ih ψ hψ0 hψ1 A0 B1 hA0 hB1
    have indV : wprob ψ (disjointOccurrence A1 B0) ≤ a1 * b0 := ih ψ hψ0 hψ1 A1 B0 hA1 hB0
    have indA1B1 : wprob ψ (disjointOccurrence A1 B1) ≤ a1 * b1 := ih ψ hψ0 hψ1 A1 B1 hA1 hB1
    set U := disjointOccurrence A0 B1 with hU
    set V := disjointOccurrence A1 B0 with hV
    set m := wprob ψ (disjointOccurrence A0 B0) with hm
    have hsubUcapV : disjointOccurrence A0 B0 ⊆ U ∩ V :=
      Set.subset_inter (disjointOccurrence_mono (le_refl _) hB01)
        (disjointOccurrence_mono hA01 (le_refl _))
    have hUVsub : U ∪ V ⊆ disjointOccurrence A1 B1 :=
      Set.union_subset (disjointOccurrence_mono hA01 (le_refl _))
        (disjointOccurrence_mono (le_refl _) hB01)
    set c0 := wprob ψ (slice (disjointOccurrence A B) false) with hc0
    set c1 := wprob ψ (slice (disjointOccurrence A B) true) with hc1
    have hc0m : c0 ≤ m := wprob_mono hψ0 slice_disjointOccurrence_false
    have hc1UV : c1 ≤ wprob ψ (U ∪ V) := wprob_mono hψ0 slice_disjointOccurrence_true
    have hincl : wprob ψ (U ∪ V) = wprob ψ U + wprob ψ V - wprob ψ (U ∩ V) := by
      have := wprob_union_inter ψ U V; linarith
    have hmUV : m ≤ wprob ψ (U ∩ V) := wprob_mono hψ0 hsubUcapV
    have hc1u : c1 ≤ a0 * b1 + a1 * b0 - m := by
      calc c1 ≤ wprob ψ (U ∪ V) := hc1UV
        _ = wprob ψ U + wprob ψ V - wprob ψ (U ∩ V) := hincl
        _ ≤ a0 * b1 + a1 * b0 - m := by linarith [indU, indV, hmUV]
    have hc1v : c1 ≤ a1 * b1 :=
      calc c1 ≤ wprob ψ (U ∪ V) := hc1UV
        _ ≤ wprob ψ (disjointOccurrence A1 B1) := wprob_mono hψ0 hUVsub
        _ ≤ a1 * b1 := indA1B1
    have hmab : m ≤ a0 * b0 := indA0B0
    have hdec : wprob φ (disjointOccurrence A B) = q * c0 + p * c1 := by rw [wprob_slice]
    have hAdec : wprob φ A = q * a0 + p * a1 := by rw [wprob_slice]
    have hBdec : wprob φ B = q * b0 + p * b1 := by rw [wprob_slice]
    rw [hdec, hAdec, hBdec]
    exact bk_algebra a0 a1 b0 b1 p q c0 c1 m hqeq hp0 hq0 hmab hc0m hc1u hc1v


end StatMech
