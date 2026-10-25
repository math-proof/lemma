/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part7
import Def.StatisticalMechanics.Code.Onsager.DecorationLoopClassification.Part4


namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_decLoopOrientation_mem
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S)
    (orientation : Fin n ⊕ Fin n) :
    ons_decLoopOrientation L d orientation ∈
      ons_decSquarefreeLoopFinset L a b S := by
  rw [ons_mem_decSquarefreeLoopFinset] at hd ⊢
  let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hd.2
  cases orientation with
  | inl k =>
      exact ⟨(ons_decLoopExponent_rotate L d k).trans hd.1,
        by simpa [ons_decLoopOrientation,
          ons_decLoopScalar_rotate] using hd.2⟩
  | inr k =>
      refine ⟨?_, ?_⟩
      · rw [ons_decLoopOrientation, ons_decLoopExponent_rotate,
          ons_decLoopExponent_loopRev L d hvalid, hd.1]
      · rw [ons_decLoopOrientation, ons_decLoopScalar_rotate,
          ons_decLoopScalar_loopRev_spin]
        exact hd.2

theorem ons_decLoopOrientation_injective
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
    Function.Injective (ons_decLoopOrientation L d) := by
  have hport := ons_decLoop_portEdge_injective_of_squarefree
    L d hvalid S hexponent
  intro x y hxy
  have hzero := congrFun hxy 0
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          have hij : i = j := by
            apply hport
            simpa [ons_decLoopOrientation, ons_rotate] using
              congrArg (ons_portEdge L) hzero
          subst j
          rfl
      | inr j =>
          exfalso
          have hbad : d i = ons_dartRev L (d (-j)) := by
            simpa [ons_decLoopOrientation, ons_rotate, ons_loopRev] using hzero
          exact ons_decLoop_dart_ne_rev_of_squarefree
            L d hvalid S hexponent i (-j) hbad
  | inr i =>
      cases y with
      | inl j =>
          exfalso
          have hbad : d j = ons_dartRev L (d (-i)) := by
            simpa [ons_decLoopOrientation, ons_rotate, ons_loopRev] using hzero.symm
          exact ons_decLoop_dart_ne_rev_of_squarefree
            L d hvalid S hexponent j (-i) hbad
      | inr j =>
          have hrev : d (-i) = d (-j) := by
            have h := congrArg (ons_dartRev L) hzero
            simp only [ons_decLoopOrientation, ons_rotate, ons_loopRev,
              zero_add] at h
            rw [ons_dartRev_involutive, ons_dartRev_involutive] at h
            exact h
          have hneg : -i = -j := by
            apply hport
            exact congrArg (ons_portEdge L) hrev
          have hij : i = j := by
            simpa using congrArg Neg.neg hneg
          subst j
          rfl

theorem ons_decSquarefreeLoopFinset_card_le
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset (n := n) L a b S) :
    (ons_decSquarefreeLoopFinset (n := n) L a b S).card ≤ 2 * n := by
  let loops := ons_decSquarefreeLoopFinset (n := n) L a b S
  let roots := loops.image (fun e ↦ e 0)
  have hcardRoots : roots.card = loops.card := by
    apply Finset.card_image_of_injOn
    exact ons_decSquarefreeLoop_eval_zero_injective L a b S
  rw [ons_mem_decSquarefreeLoopFinset] at hd
  let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hd.2
  have hsubset : roots ⊆ ons_decLoopRootFinset L d := by
    intro root hroot
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hroot
    apply ons_external_root_mem_decLoopRootFinset
      L d hvalid S hd.1 (e 0)
    apply ons_decSquarefreeLoop_root_edge_mem L a b S
    exact he
  calc
    (ons_decSquarefreeLoopFinset (n := n) L a b S).card = roots.card := by
      exact hcardRoots.symm
    _ ≤ (ons_decLoopRootFinset L d).card :=
      Finset.card_le_card hsubset
    _ = 2 * n := ons_decLoopRootFinset_card_of_squarefree
      L d hvalid S hd.1

theorem ons_decSquarefreeLoopFinset_card_ge
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset (n := n) L a b S) :
    2 * n ≤ (ons_decSquarefreeLoopFinset (n := n) L a b S).card := by
  let loops := ons_decSquarefreeLoopFinset (n := n) L a b S
  let orient : Fin n ⊕ Fin n → {e // e ∈ loops} := fun k ↦
    ⟨ons_decLoopOrientation L d k,
      ons_decLoopOrientation_mem L a b S hd k⟩
  have hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d
    ((ons_mem_decSquarefreeLoopFinset L a b S d).mp hd).2
  have horient : Function.Injective orient := by
    intro i j hij
    apply ons_decLoopOrientation_injective L d hvalid S
      ((ons_mem_decSquarefreeLoopFinset L a b S d).mp hd).1
    exact congrArg Subtype.val hij
  have hcard := Fintype.card_le_of_injective orient horient
  simpa [loops, Fintype.card_sum, two_mul] using hcard

theorem ons_decSquarefreeLoopFinset_card
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset (n := n) L a b S) :
    (ons_decSquarefreeLoopFinset (n := n) L a b S).card = 2 * n := by
  apply Nat.le_antisymm
  · exact ons_decSquarefreeLoopFinset_card_le L a b S hd
  · exact ons_decSquarefreeLoopFinset_card_ge L a b S hd

theorem ons_decLoopRootFinset_mem_external
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S)
    (root : ons_Dart L) :
    root ∈ ons_decLoopRootFinset L d ↔
      s(root, ons_dartRev L root) ∈ S := by
  constructor
  · intro hroot
    unfold ons_decLoopRootFinset at hroot
    rw [Finset.mem_union] at hroot
    rcases hroot with hroot | hroot
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hroot
      let q := ons_decLoopWalk L d hvalid
      have hmem : d k ∈ ons_decWalkExternalDarts q := by
        rw [ons_decLoopWalk_externalDarts L d hvalid, List.mem_ofFn]
        exact ⟨-k, by simp [ons_decGeometricLoopStates]⟩
      have hedge := ons_externalEdge_mem_edges_of_mem_decWalkExternalDarts q hmem
      rw [← ons_decLoopWalk_edges_toFinset_of_squarefree
        L d hvalid S hexponent]
      exact List.mem_toFinset.mpr hedge
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hroot
      rw [ons_dartRev_involutive, Sym2.eq_swap]
      let q := ons_decLoopWalk L d hvalid
      have hmem : d k ∈ ons_decWalkExternalDarts q := by
        rw [ons_decLoopWalk_externalDarts L d hvalid, List.mem_ofFn]
        exact ⟨-k, by simp [ons_decGeometricLoopStates]⟩
      have hedge := ons_externalEdge_mem_edges_of_mem_decWalkExternalDarts q hmem
      rw [← ons_decLoopWalk_edges_toFinset_of_squarefree
        L d hvalid S hexponent]
      exact List.mem_toFinset.mpr hedge
  · exact ons_external_root_mem_decLoopRootFinset
      L d hvalid S hexponent root

theorem ons_decSquarefreeLoop_length_unique
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n m : ℕ} [NeZero n] [NeZero m]
    (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L} {e : Fin m → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S)
    (he : e ∈ ons_decSquarefreeLoopFinset L a b S) :
    n = m := by
  rw [ons_mem_decSquarefreeLoopFinset] at hd he
  let hdvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hd.2
  let hevalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) e he.2
  have hroots : ons_decLoopRootFinset L d = ons_decLoopRootFinset L e := by
    ext root
    rw [ons_decLoopRootFinset_mem_external L d hdvalid S hd.1,
      ons_decLoopRootFinset_mem_external L e hevalid S he.1]
  have hcard := congrArg Finset.card hroots
  rw [ons_decLoopRootFinset_card_of_squarefree L d hdvalid S hd.1,
    ons_decLoopRootFinset_card_of_squarefree L e hevalid S he.1] at hcard
  omega

theorem ons_walkOriginalEdges_eq_of_edges_toFinset_eq
    {L : ℕ} [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u u)
    (q : (ons_decGraph L).Walk v v)
    (hedges : p.edges.toFinset = q.edges.toFinset) :
    ons_walkOriginalEdges p = ons_walkOriginalEdges q := by
  unfold ons_walkOriginalEdges ons_walkExternalEdges
  rw [hedges]

theorem ons_decSquarefreeLoop_scalar_eq
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n m : ℕ} [NeZero n] [NeZero m]
    (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L} {e : Fin m → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S)
    (he : e ∈ ons_decSquarefreeLoopFinset L a b S) :
    ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) d =
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) e := by
  rw [ons_mem_decSquarefreeLoopFinset] at hd he
  let hdvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hd.2
  let hevalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) e he.2
  have horiginal :
      ons_walkOriginalEdges (ons_decLoopWalk L d hdvalid) =
        ons_walkOriginalEdges (ons_decLoopWalk L e hevalid) := by
    apply ons_walkOriginalEdges_eq_of_edges_toFinset_eq
    rw [ons_decLoopWalk_edges_toFinset_of_squarefree
        L d hdvalid S hd.1,
      ons_decLoopWalk_edges_toFinset_of_squarefree
        L e hevalid S he.1]
  have hhomology :
      ons_evenHomology L
          (ons_walkOriginalEdges (ons_decLoopWalk L d hdvalid)) =
        ons_evenHomology L
          (ons_walkOriginalEdges (ons_decLoopWalk L e hevalid)) :=
    congrArg (ons_evenHomology L) horiginal
  have hdscalar := ons_decLoopScalar_eq_neg_spinCharacter_of_squarefree
    L a b d S hd.1 hd.2
  have hescalar := ons_decLoopScalar_eq_neg_spinCharacter_of_squarefree
    L a b e S he.1 he.2
  calc
    ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) d =
        -((ons_spinCharacter a b
          (ons_evenHomology L
            (ons_walkOriginalEdges (ons_decLoopWalk L d hdvalid))) : ℂ)) := by
      simpa only [hdvalid] using hdscalar
    _ = -((ons_spinCharacter a b
          (ons_evenHomology L
            (ons_walkOriginalEdges (ons_decLoopWalk L e hevalid))) : ℂ)) := by
      rw [hhomology]
    _ = ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) e := by
      simpa only [hevalid] using hescalar.symm

theorem ons_decSquarefreeLoop_bucket_sum
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
    (∑ e : Fin n → ons_Dart L,
      if ons_decLoopExponent L e = ons_finsetExponent S then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) e
      else 0) =
      (2 * n : ℂ) *
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) d := by
  classical
  let loops := ons_decSquarefreeLoopFinset (n := n) L a b S
  calc
    (∑ e : Fin n → ons_Dart L,
      if ons_decLoopExponent L e = ons_finsetExponent S then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) e
      else 0) =
        ∑ e ∈ loops,
          ons_decLoopScalar L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) e := by
      rw [← Finset.sum_filter]
      symm
      apply Finset.sum_subset
      · intro e he
        simp only [loops, ons_decSquarefreeLoopFinset,
          Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        exact he.1
      · intro e heExp heNot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heExp
        by_contra hscalar
        apply heNot
        simp [loops, ons_decSquarefreeLoopFinset, heExp, hscalar]
    _ = ∑ _e ∈ loops,
          ons_decLoopScalar L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) d := by
      apply Finset.sum_congr rfl
      intro e he
      exact ons_decSquarefreeLoop_scalar_eq L a b S he hd
    _ = (2 * n : ℂ) *
          ons_decLoopScalar L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) d := by
      rw [Finset.sum_const, nsmul_eq_mul,
        ons_decSquarefreeLoopFinset_card L a b S hd]
      norm_cast

theorem ons_decFormalLogCoeff_squarefree_of_mem
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L)) (r : ℕ)
    (d : Fin (r + 1) → ons_Dart L)
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
    ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_finsetExponent S) =
      (ons_spinCharacter a b
        (ons_evenHomology L
          (ons_walkOriginalEdges
            (ons_decLoopWalk L d
              (ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
                (ons_spinPhase L a) (ons_spinPhase L b) d
                ((ons_mem_decSquarefreeLoopFinset L a b S d).mp hd).2)))) : ℂ) := by
  have hddata := (ons_mem_decSquarefreeLoopFinset L a b S d).mp hd
  let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hddata.2
  change ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)
      (ons_finsetExponent S) =
    (ons_spinCharacter a b
      (ons_evenHomology L
        (ons_walkOriginalEdges (ons_decLoopWalk L d hvalid))) : ℂ)
  have hlength := ons_decLoopExponent_length_le L d
  rw [hddata.1] at hlength
  have hrange : r ∈ Finset.range
      (ons_finsuppTotalDegree (ons_finsetExponent S)) := by
    rw [Finset.mem_range]
    omega
  unfold ons_decFormalLogCoeff
  rw [Finset.sum_eq_single r]
  · rw [ons_decSquarefreeLoop_bucket_sum L a b S hd]
    have hscalar := ons_decLoopScalar_eq_neg_spinCharacter_of_squarefree
      L a b d S hddata.1 hddata.2
    have hscalar' :
        ons_decLoopScalar L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) d =
          -((ons_spinCharacter a b
            (ons_evenHomology L
              (ons_walkOriginalEdges
                (ons_decLoopWalk L d hvalid))) : ℂ)) := by
      simpa only [hvalid] using hscalar
    calc
      (-(2 * ((r + 1 : ℕ) : ℂ) *
            ons_decLoopScalar L ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b) d /
            ((r : ℂ) + 1))) / 2 =
          -ons_decLoopScalar L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) d := by
        push_cast
        field_simp
      _ = -(-((ons_spinCharacter a b
            (ons_evenHomology L
              (ons_walkOriginalEdges
                (ons_decLoopWalk L d hvalid))) : ℂ))) :=
        congrArg Neg.neg hscalar'
      _ = (ons_spinCharacter a b
            (ons_evenHomology L
              (ons_walkOriginalEdges
                (ons_decLoopWalk L d hvalid))) : ℂ) := by ring
  · intro r' hr' hne
    apply div_eq_zero_iff.mpr
    left
    apply Finset.sum_eq_zero
    intro e he
    by_cases hexp : ons_decLoopExponent L e = ons_finsetExponent S
    · by_cases hscalar : ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) e = 0
      · simp [hexp, hscalar]
      · exfalso
        have heMem : e ∈ ons_decSquarefreeLoopFinset L a b S :=
          (ons_mem_decSquarefreeLoopFinset L a b S e).mpr
            ⟨hexp, hscalar⟩
        have hlen := ons_decSquarefreeLoop_length_unique
          L a b S hd heMem
        omega
    · simp [hexp]
  · intro hnot
    exact (hnot hrange).elim

theorem ons_decFormalLogCoeff_squarefree_eq_zero_of_empty
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L))
    (hempty : ∀ r : ℕ,
      (ons_decSquarefreeLoopFinset (n := r + 1) L a b S).Nonempty → False) :
    ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_finsetExponent S) = 0 := by
  unfold ons_decFormalLogCoeff
  suffices hsum : ∀ r : ℕ,
      (∑ d : Fin (r + 1) → ons_Dart L,
        if ons_decLoopExponent L d = ons_finsetExponent S then
          ons_decLoopScalar L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) d
        else 0) = 0 by
    simp [hsum]
  intro r
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hexp : ons_decLoopExponent L d = ons_finsetExponent S
  · by_cases hscalar : ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) d = 0
    · simp [hexp, hscalar]
    · exfalso
      apply hempty r
      refine ⟨d, ?_⟩
      exact (ons_mem_decSquarefreeLoopFinset L a b S d).mpr
        ⟨hexp, hscalar⟩
  · simp [hexp]

theorem ons_decFormalLogCoeff_squarefree_cases
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L)) :
    ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_finsetExponent S) = 0 ∨
      ∃ (r : ℕ) (d : Fin (r + 1) → ons_Dart L)
        (hd : d ∈ ons_decSquarefreeLoopFinset L a b S),
        ons_decFormalLogCoeff L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b)
            (ons_finsetExponent S) =
          (ons_spinCharacter a b
            (ons_evenHomology L
              (ons_walkOriginalEdges
                (ons_decLoopWalk L d
                  (ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
                    (ons_spinPhase L a) (ons_spinPhase L b) d
                    ((ons_mem_decSquarefreeLoopFinset L a b S d).mp hd).2)))) : ℂ) := by
  classical
  by_cases hexists : ∃ r : ℕ,
      (ons_decSquarefreeLoopFinset (n := r + 1) L a b S).Nonempty
  · right
    obtain ⟨r, d, hd⟩ := hexists
    exact ⟨r, d, hd,
      ons_decFormalLogCoeff_squarefree_of_mem L a b S r d hd⟩
  · left
    apply ons_decFormalLogCoeff_squarefree_eq_zero_of_empty L a b S
    intro r hr
    exact hexists ⟨r, hr⟩

theorem ons_decSquarefreeLoop_edges_even
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
    S ∈ StatMech.Ising.evenSubgraphs (ons_decGraph L) := by
  rw [ons_mem_decSquarefreeLoopFinset] at hd
  let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hd.2
  let q := ons_decLoopWalk L d hvalid
  have hq : q.IsCycle :=
    ons_decLoopWalk_isCycle_of_squarefree L d hvalid S hd.1
  rw [← ons_decLoopWalk_edges_toFinset_of_squarefree
    L d hvalid S hd.1]
  exact ons_cycle_edges_evenSubgraph (ons_decGraph L) q hq

end StatMech.Onsager
