/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part2


namespace StatMech.Onsager

open BigOperators Finset

section PathSum

variable {E M : Type*} [AddCommMonoid M]

@[simp] theorem ons_pathSum_nil (step : E → E → M) :
    ons_pathSum step [] = 0 := rfl

@[simp] theorem ons_pathSum_singleton (step : E → E → M) (x : E) :
    ons_pathSum step [x] = 0 := rfl

theorem ons_pathSum_cons_cons (step : E → E → M)
    (x y : E) (tail : List E) :
    ons_pathSum step (x :: y :: tail) =
      step x y + ons_pathSum step (y :: tail) := rfl

theorem ons_pathSum_append_cons (step : E → E → M)
    (pre : List E) (x : E) (suffix : List E) :
    ons_pathSum step (pre ++ x :: suffix) =
      ons_pathSum step (pre ++ [x]) + ons_pathSum step (x :: suffix) := by
  induction pre with
  | nil => simp
  | cons a tail ih =>
      cases tail with
      | nil =>
          simp [ons_pathSum]
      | cons b tail =>
          simp only [List.cons_append, ons_pathSum_cons_cons]
          simpa only [List.cons_append, add_assoc] using
            congrArg (fun z ↦ step a b + z) ih

theorem ons_pathSum_glue (step : E → E → M) (root : E)
    (segments : List (List E))
    (hhead : ∀ segment ∈ segments, segment.head? = some root)
    (hlast : ∀ segment ∈ segments, segment.getLast? = some root) :
    ons_pathSum step (ons_glue root segments) =
      (segments.map (ons_pathSum step)).sum := by
  induction segments with
  | nil => simp [ons_glue]
  | cons segment segments ih =>
      have hsegmentHead := hhead segment (by simp)
      have hsegmentLast := hlast segment (by simp)
      have hhead' : ∀ s ∈ segments, s.head? = some root :=
        fun s hs ↦ hhead s (by simp [hs])
      have hlast' : ∀ s ∈ segments, s.getLast? = some root :=
        fun s hs ↦ hlast s (by simp [hs])
      obtain ⟨tail, htail⟩ := ons_glue_head root segments hhead'
      have hne : segment ≠ [] := by
        rintro rfl
        simp at hsegmentHead
      have hreconstruct : segment.dropLast ++ [root] = segment :=
        List.dropLast_append_getLast? root hsegmentLast
      rw [ons_glue_cons, htail,
        ons_pathSum_append_cons, ← htail, hreconstruct,
        ih hhead' hlast']
      simp

theorem ons_pathSum_ofFn (step : E → E → M) (n : ℕ)
    (f : Fin (n + 1) → E) :
    ons_pathSum step (List.ofFn f) =
      ∑ i : Fin n, step (f i.castSucc) (f i.succ) := by
  induction n with
  | zero => simp [List.ofFn_succ]
  | succ n ih =>
      rw [List.ofFn_succ]
      let g : Fin (n + 1) → E := fun i ↦ f i.succ
      have hg : List.ofFn g = g 0 :: List.ofFn (fun i : Fin n ↦ g i.succ) := by
        rw [List.ofFn_succ]
      rw [hg, ons_pathSum_cons_cons, ← hg, ih g, Fin.sum_univ_succ]
      simp only [g, Fin.castSucc_zero, Fin.succ_castSucc]

theorem ons_cyclicSum_eq_pathSum (step : E → E → M)
    {n : ℕ} (loop : Fin (n + 1) → E) :
    (∑ k, step (loop k) (loop (k + 1))) =
      ons_pathSum step (List.ofFn loop ++ [loop 0]) := by
  have hlist : List.ofFn loop ++ [loop 0] =
      List.ofFn (Fin.snoc loop (loop 0) : Fin (n + 2) → E) := by
    rw [List.ofFn_succ' (Fin.snoc loop (loop 0) : Fin (n + 2) → E)]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hlist, ons_pathSum_ofFn]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Fin.snoc_castSucc, ons_snoc_succ]

end PathSum

theorem ons_decLoopExponent_eq_pathSum
    (L : ℕ) {n : ℕ} (loop : Fin (n + 1) → ons_Dart L) :
    ons_decLoopExponent L loop =
      ons_pathSum (ons_decTransitionExponent L)
        (List.ofFn loop ++ [loop 0]) := by
  unfold ons_decLoopExponent
  exact ons_cyclicSum_eq_pathSum (ons_decTransitionExponent L) loop

theorem ons_decLoopExponent_eq_firstReturnFactors_sum
    (L : ℕ) {n : ℕ} (d : ons_Dart L)
    (loop : Fin (n + 1) → ons_Dart L) (hroot : loop 0 = d) :
    ons_decLoopExponent L loop =
      ((ons_firstReturnFactors d (List.ofFn loop ++ [d])).map
        (ons_pathSum (ons_decTransitionExponent L))).sum := by
  let closed := List.ofFn loop ++ [d]
  have hclosed : List.ofFn loop ++ [loop 0] = closed := by
    rw [hroot]
  have hhead : closed.head? = some d := by
    rw [show closed = List.ofFn loop ++ [d] from rfl]
    simp [List.ofFn_succ, hroot]
  have hlast : closed.getLast? = some d := by
    rw [show closed = List.ofFn loop ++ [d] from rfl,
      List.getLast?_append_of_ne_nil _ (by simp : [d] ≠ [])]
    simp
  have hspec := ons_firstReturnFactors_spec d closed hhead hlast
  rw [ons_decLoopExponent_eq_pathSum, hclosed, ← hspec.2.2]
  apply ons_pathSum_glue
  · intro segment hsegment
    exact ons_firstReturnSegment_head (hspec.2.1 segment hsegment)
  · intro segment hsegment
    exact ons_firstReturnSegment_last (hspec.2.1 segment hsegment)

theorem ons_decLoopScalar_eq_firstReturnFactors_prod
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} (d : ons_Dart L)
    (loop : Fin (n + 1) → ons_Dart L) (hroot : loop 0 = d) :
    ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) loop =
      ((ons_firstReturnFactors d (List.ofFn loop ++ [d])).map
        (ons_edgeWeight (ons_KWmatWeightedPhase L (fun _ ↦ 1)
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)))).prod := by
  let Lambda := ons_KWmatWeightedPhase L (fun _ ↦ 1)
    ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)
  let closed := List.ofFn loop ++ [d]
  have hclosed : List.ofFn loop ++ [loop 0] = closed := by
    rw [hroot]
  have hhead : closed.head? = some d := by
    rw [show closed = List.ofFn loop ++ [d] from rfl]
    simp [List.ofFn_succ, hroot]
  have hlast : closed.getLast? = some d := by
    rw [show closed = List.ofFn loop ++ [d] from rfl,
      List.getLast?_append_of_ne_nil _ (by simp : [d] ≠ [])]
    simp
  have hspec := ons_firstReturnFactors_spec d closed hhead hlast
  rw [ons_decLoopScalar_eq_loopWeight_one,
    ons_loopWeight_eq_edgeWeight, hclosed, ← hspec.2.2]
  exact ons_edgeWeight_glue Lambda d _
    (fun segment hsegment ↦
      ons_firstReturnSegment_head (hspec.2.1 segment hsegment))
    (fun segment hsegment ↦
      ons_firstReturnSegment_last (hspec.2.1 segment hsegment))

theorem ons_firstReturnSegment_eq_closedFinLoop
    {E : Type*} {d : E} {segment : List E}
    (hsegment : ons_isFirstReturnSegment d segment) :
    ∃ (n : ℕ) (loop : Fin (n + 1) → E),
      loop 0 = d ∧
      (∀ k, k ≠ 0 → loop k ≠ d) ∧
      segment = List.ofFn loop ++ [d] := by
  obtain ⟨interior, hform, hinterior⟩ := hsegment
  let loop : Fin (interior.length + 1) → E :=
    (d :: interior).get
  refine ⟨interior.length, loop, ?_, ?_, ?_⟩
  · simp [loop]
  · intro k
    refine Fin.cases (motive := fun k ↦ k ≠ 0 → loop k ≠ d) ?_ ?_ k
    · intro hk
      exact (hk rfl).elim
    · intro j hk
      simpa [loop] using hinterior (interior.get j) (List.get_mem interior j)
  · rw [hform]
    have hofFn : List.ofFn loop = d :: interior := by
      exact List.ofFn_get (d :: interior)
    rw [hofFn]

theorem ons_closedFinLoop_isFirstReturnSegment
    {E : Type*} {n : ℕ} {d : E} (loop : Fin (n + 1) → E)
    (hroot : loop 0 = d)
    (hfirst : ∀ k, k ≠ 0 → loop k ≠ d) :
    ons_isFirstReturnSegment d (List.ofFn loop ++ [d]) := by
  let interior := List.ofFn (fun k : Fin n ↦ loop k.succ)
  refine ⟨interior, ?_, ?_⟩
  · rw [List.ofFn_succ]
    exact congrArg (fun x ↦ x :: interior ++ [d]) hroot
  · intro x hx
    rw [show interior = List.ofFn (fun k : Fin n ↦ loop k.succ) from rfl,
      List.mem_ofFn] at hx
    obtain ⟨k, rfl⟩ := hx
    exact hfirst k.succ (by simp)

theorem ons_firstReturnSegment_avoids_of_closedLoop
    {L n : ℕ} [Fact (2 < L)]
    (d : ons_Dart L) (loop : Fin (n + 1) → ons_Dart L)
    (havoid : ∀ k, loop k ≠ ons_dartRev L d) :
    ∀ x ∈ List.ofFn loop ++ [d], x ≠ ons_dartRev L d := by
  intro x hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · rw [List.mem_ofFn] at hx
    obtain ⟨k, rfl⟩ := hx
    exact havoid k
  · simp only [List.mem_singleton] at hx
    subst x
    exact (ons_dartRev_ne L d).symm

theorem ons_decFirstReturnSegment_pathSum_eq_loopExponent
    (L : ℕ) {n : ℕ} (d : ons_Dart L)
    (loop : Fin (n + 1) → ons_Dart L)
    (hroot : loop 0 = d) :
    ons_pathSum (ons_decTransitionExponent L) (List.ofFn loop ++ [d]) =
      ons_decLoopExponent L loop := by
  rw [← hroot]
  exact (ons_decLoopExponent_eq_pathSum L loop).symm

theorem ons_decFirstReturnSegment_edgeWeight_eq_loopScalar
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} (d : ons_Dart L)
    (loop : Fin (n + 1) → ons_Dart L)
    (hroot : loop 0 = d) :
    ons_edgeWeight
        (ons_KWmatWeightedPhase L (fun _ ↦ 1) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        (List.ofFn loop ++ [d]) =
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) loop := by
  rw [← hroot, ← ons_loopWeight_eq_edgeWeight,
    ons_decLoopScalar_eq_loopWeight_one]


end StatMech.Onsager
