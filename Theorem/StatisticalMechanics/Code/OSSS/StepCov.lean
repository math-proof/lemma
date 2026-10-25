/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part6
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace StepCov

open OSSS.Monotonic OSSS.Coding OSSS.Lindeberg OSSS.LindebergTree

open OSSS.DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma abs_coord_sub_eq (e : E) (ω : ConfigSpace E) {N : ℝ} (hN0 : 0 ≤ N) (hN1 : N ≤ 1) :
    |coord e ω - N| = coord e ω + N - 2 * coord e ω * N := by
  unfold coord
  by_cases hb : ω e
  · simp only [hb, if_true]
    rw [abs_of_nonneg (by linarith)]; ring
  · simp only [hb, Bool.false_eq_true, if_false]
    rw [abs_of_nonpos (by linarith)]; ring


lemma mean_Fmeas_mul_abs_coord_sub {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (e : E) {g : ConfigSpace E → ℝ} (hg : Fmeas F g) :
    mean μ (fun ω => g ω * |coord e ω - cExp μ F (coord e) ω|)
      = 2 * mean μ (fun ω => g ω * (cExp μ F (coord e) ω * (1 - cExp μ F (coord e) ω))) := by
  set N := cExp μ F (coord e) with hNdef
  
  have hN0 : ∀ ω, 0 ≤ N ω := fun ω => cExp_nonneg hpos F (coord_nonneg e) ω
  have hN1 : ∀ ω, N ω ≤ 1 := fun ω =>
    cExp_le_one hpos F (fun ω => by unfold coord; split <;> norm_num) ω
  
  have hexp : mean μ (fun ω => g ω * |coord e ω - N ω|)
      = mean μ (fun ω => g ω * coord e ω) + mean μ (fun ω => g ω * N ω)
        - 2 * mean μ (fun ω => g ω * coord e ω * N ω) := by
    unfold mean
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    simp only []
    rw [abs_coord_sub_eq e ω (hN0 ω) (hN1 ω)]; ring
  rw [hexp]
  
  have hpull1 : mean μ (fun ω => g ω * coord e ω) = mean μ (fun ω => g ω * N ω) := by
    have hp := cExp_pullout hpos F (coord e) g hg
    unfold mean
    rw [show (fun ω => g ω * coord e ω) = (fun ω => coord e ω * g ω) from by funext ω; ring]
    rw [show (∑ ω, (fun ω => coord e ω * g ω) ω * μ ω) = ∑ ω, (coord e ω * g ω) * μ ω from rfl, ← hp]
    rw [hNdef]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  
  have hgN_Fmeas : Fmeas F (fun ω => g ω * N ω) := by
    intro η η' h
    have h1 := hg η η' h
    have h2 : N η = N η' := (cExp_Fmeas μ F (coord e)) η η' h
    show g η * N η = g η' * N η'; rw [h1, h2]
  have hpull2 : mean μ (fun ω => g ω * coord e ω * N ω) = mean μ (fun ω => g ω * N ω * N ω) := by
    have hp := cExp_pullout hpos F (coord e) (fun ω => g ω * N ω) hgN_Fmeas
    unfold mean
    rw [show (fun ω => g ω * coord e ω * N ω) = (fun ω => coord e ω * (g ω * N ω)) from by
          funext ω; ring]
    rw [show (∑ ω, (fun ω => coord e ω * (g ω * N ω)) ω * μ ω)
          = ∑ ω, (coord e ω * (g ω * N ω)) * μ ω from rfl, ← hp]
    rw [hNdef]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  rw [hpull1, hpull2]
  
  unfold mean
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  simp only []
  ring


lemma abs_step_eq_delta_mul {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hFKG : FKGLatticeCondition μ) (F : Finset E) (e : E) (he : e ∉ F)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (ω : ConfigSpace E) :
    |cExp μ (insert e F) f ω - cExp μ F f ω|
      = delta μ F e f ω * |coord e ω - cExp μ F (coord e) ω| := by
  rw [step_factor hpos F e he f ω, abs_mul,
      abs_of_nonneg (delta_nonneg hpos hFKG F e hf hf0 ω)]


lemma stepAbs_eq_two_mul {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hFKG : FKGLatticeCondition μ) (F : Finset E) (e : E) (he : e ∉ F)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    {g : ConfigSpace E → ℝ} (hg : Fmeas F g) :
    mean μ (fun ω => g ω * |cExp μ (insert e F) f ω - cExp μ F f ω|)
      = 2 * mean μ (fun ω => (g ω * delta μ F e f ω)
            * (cExp μ F (coord e) ω * (1 - cExp μ F (coord e) ω))) := by
  
  have hrw : (fun ω => g ω * |cExp μ (insert e F) f ω - cExp μ F f ω|)
      = (fun ω => (fun ω => g ω * delta μ F e f ω) ω * |coord e ω - cExp μ F (coord e) ω|) := by
    funext ω
    rw [abs_step_eq_delta_mul hpos hFKG F e he hf hf0 ω]; ring
  rw [hrw]
  
  have hgδ : Fmeas F (fun ω => g ω * delta μ F e f ω) := by
    intro η η' h
    have h1 := hg η η' h
    have h2 := (delta_Fmeas μ F e he f) η η' h
    show g η * delta μ F e f η = g η' * delta μ F e f η'; rw [h1, h2]
  exact mean_Fmeas_mul_abs_coord_sub hpos F e hgδ


lemma pathPrefix_eq_of_agree (T : DecisionTree E) (ω ω' : ConfigSpace E) (t : ℕ)
    (h : Agree (pathPrefix T ω t) ω ω') :
    pathPrefix T ω' t = pathPrefix T ω t := by
  induction T generalizing t ω' with
  | leaf b => rw [pathPrefix_leaf, pathPrefix_leaf]
  | node eN l r IHl IHr =>
    cases t with
    | zero => rw [pathPrefix_zero, pathPrefix_zero]
    | succ k =>
      rw [pathPrefix_node_succ] at h ⊢
      have heN : ω' eN = ω eN := h eN (Finset.mem_insert_self eN _)
      rw [heN]
      have hbr : Agree (pathPrefix (if ω eN then l else r) ω k) ω ω' := by
        intro x hx; exact h x (Finset.mem_insert_of_mem hx)
      congr 1
      by_cases hb : ω eN
      · simp only [hb, if_true] at hbr ⊢; exact IHl ω' k hbr
      · simp only [hb, Bool.false_eq_true, if_false] at hbr ⊢; exact IHr ω' k hbr


lemma pathPrefix_succ_eq_of_agree (T : DecisionTree E) (ω ω' : ConfigSpace E) (t : ℕ)
    (h : Agree (pathPrefix T ω t) ω ω') :
    pathPrefix T ω' (t + 1) = pathPrefix T ω (t + 1) := by
  induction T generalizing t ω' with
  | leaf b => rw [pathPrefix_leaf, pathPrefix_leaf]
  | node eN l r IHl IHr =>
    cases t with
    | zero =>
      rw [pathPrefix_node_succ, pathPrefix_node_succ, pathPrefix_zero, pathPrefix_zero]
    | succ k =>
      rw [pathPrefix_node_succ] at h
      have heN : ω' eN = ω eN := h eN (Finset.mem_insert_self eN _)
      rw [pathPrefix_node_succ, pathPrefix_node_succ, heN]
      have hbr : Agree (pathPrefix (if ω eN then l else r) ω k) ω ω' := by
        intro x hx; exact h x (Finset.mem_insert_of_mem hx)
      congr 1
      by_cases hb : ω eN
      · simp only [hb, if_true] at hbr ⊢; exact IHl ω' k hbr
      · simp only [hb, Bool.false_eq_true, if_false] at hbr ⊢; exact IHr ω' k hbr


lemma pathPrefix_eq_Fmeas (T : DecisionTree E) (F : Finset E) (t : ℕ) :
    Fmeas F (fun ω => if pathPrefix T ω t = F then (1 : ℝ) else 0) := by
  intro η η' h
  show (if pathPrefix T η t = F then (1 : ℝ) else 0)
      = (if pathPrefix T η' t = F then (1 : ℝ) else 0)
  by_cases hη : pathPrefix T η t = F
  · 
    have hag : Agree (pathPrefix T η t) η η' := by
      intro x hx; rw [hη] at hx; exact (h x hx).symm
    have heq : pathPrefix T η' t = pathPrefix T η t := pathPrefix_eq_of_agree T η η' t hag
    rw [if_pos hη, if_pos (by rw [heq, hη])]
  · 
    have hη' : pathPrefix T η' t ≠ F := by
      intro hcontra
      apply hη
      have hag : Agree (pathPrefix T η' t) η' η := by
        intro x hx; rw [hcontra] at hx; exact h x hx
      rw [pathPrefix_eq_of_agree T η' η t hag, hcontra]
    rw [if_neg hη, if_neg hη']


lemma freshPref_Fmeas (T : DecisionTree E) (F : Finset E) (e : E) (t : ℕ) :
    Fmeas F (fun ω =>
      if pathPrefix T ω t = F ∧ pathPrefix T ω (t + 1) = insert e F then (1 : ℝ) else 0) := by
  
  
  have key : ∀ (a b : ConfigSpace E),
      (∀ x ∈ F, a x = b x) →
      pathPrefix T a t = F → pathPrefix T a (t + 1) = insert e F →
      pathPrefix T b t = F ∧ pathPrefix T b (t + 1) = insert e F := by
    intro a b hab hat hat1
    have hag : Agree (pathPrefix T a t) a b := by
      intro x hx; rw [hat] at hx; exact (hab x hx).symm
    refine ⟨?_, ?_⟩
    · rw [pathPrefix_eq_of_agree T a b t hag, hat]
    · rw [pathPrefix_succ_eq_of_agree T a b t hag, hat1]
  intro η η' h
  show (if pathPrefix T η t = F ∧ pathPrefix T η (t + 1) = insert e F then (1 : ℝ) else 0)
      = (if pathPrefix T η' t = F ∧ pathPrefix T η' (t + 1) = insert e F then (1 : ℝ) else 0)
  by_cases hη : pathPrefix T η t = F ∧ pathPrefix T η (t + 1) = insert e F
  · obtain ⟨hηt, hηt1⟩ := hη
    rw [if_pos ⟨hηt, hηt1⟩, if_pos (key η η' h hηt hηt1)]
  · have hη' : ¬ (pathPrefix T η' t = F ∧ pathPrefix T η' (t + 1) = insert e F) := by
      rintro ⟨hη't, hη't1⟩
      exact hη (key η' η (fun x hx => (h x hx).symm) hη't hη't1)
    rw [if_neg hη, if_neg hη']


end StepCov
end OSSS
end StatMech
