/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part6
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in
theorem mem_edgeCopySourceSectorContainingAndExcludingCopy
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {inside outside : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)} :
    K ∈ edgeCopySourceSectorContainingAndExcludingCopy G A m inside outside ↔
      K ∈ edgeCopySourceSector G A m ∧ inside ∈ K ∧ outside ∉ K := by
  simp [edgeCopySourceSectorContainingAndExcludingCopy]

set_option linter.style.longLine false in
theorem edgeCopySourceSectorContainingAndExcludingCopy_nonempty_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {inside outside : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hK : K ∈ edgeCopySourceSector G A m) (hinside : inside ∈ K)
    (houtside : outside ∉ K) :
    (edgeCopySourceSectorContainingAndExcludingCopy G A m inside outside).Nonempty := by
  exact
    ⟨K,
      (mem_edgeCopySourceSectorContainingAndExcludingCopy
        (G := G) (A := A) (m := m) (inside := inside)
        (outside := outside) (K := K)).mpr
        ⟨hK, hinside, houtside⟩⟩

set_option linter.style.longLine false in
theorem edgeCopySourceSectorContainingAndExcludingCopy_card_pos_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {inside outside : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hK : K ∈ edgeCopySourceSector G A m) (hinside : inside ∈ K)
    (houtside : outside ∉ K) :
    0 <
      (edgeCopySourceSectorContainingAndExcludingCopy G A m inside outside).card :=
  Finset.Nonempty.card_pos
    (edgeCopySourceSectorContainingAndExcludingCopy_nonempty_of_mem hK hinside
      houtside)

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingCopy_branch_card_add_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ)
    (owner selected : Sharpness.FluxEdgeCopy.Copy G m) :
    (edgeCopySourceSectorContainingBothCopies G A m owner selected).card +
      (edgeCopySourceSectorContainingAndExcludingCopy G A m owner selected).card =
      (edgeCopySourceSectorContainingCopy G A m owner).card := by
  classical
  let S := edgeCopySourceSector G A m
  let P : Finset (Sharpness.FluxEdgeCopy.Copy G m) → Prop :=
    fun K => owner ∈ K
  let Q : Finset (Sharpness.FluxEdgeCopy.Copy G m) → Prop :=
    fun K => selected ∈ K
  have h := Finset.card_filter_add_card_filter_not (s := S.filter P) (p := Q)
  change ((S.filter P).filter Q).card +
      ((S.filter P).filter (fun K => ¬ Q K)).card = (S.filter P).card at h
  simpa [edgeCopySourceSectorContainingCopy,
    edgeCopySourceSectorContainingBothCopies,
    edgeCopySourceSectorContainingAndExcludingCopy, S, P, Q,
    Finset.filter_filter, and_left_comm, and_assoc]
    using h

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingCopy_card_mul_eq_both_add_excluding_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ)
    (owner selected : Sharpness.FluxEdgeCopy.Copy G m) (base : ℝ) :
    ((edgeCopySourceSectorContainingCopy G A m owner).card : ℝ) * base =
      ((edgeCopySourceSectorContainingBothCopies G A m owner selected).card :
        ℝ) * base +
        ((edgeCopySourceSectorContainingAndExcludingCopy G A m owner
          selected).card : ℝ) * base := by
  have hcard :=
    edgeCopySourceSectorContainingCopy_branch_card_add_eq G A m owner selected
  have hcast :
      ((edgeCopySourceSectorContainingBothCopies G A m owner selected).card :
          ℝ) +
        ((edgeCopySourceSectorContainingAndExcludingCopy G A m owner
          selected).card : ℝ) =
          ((edgeCopySourceSectorContainingCopy G A m owner).card : ℝ) := by
    exact_mod_cast hcard
  calc
    ((edgeCopySourceSectorContainingCopy G A m owner).card : ℝ) * base =
        (((edgeCopySourceSectorContainingBothCopies G A m owner
              selected).card : ℝ) +
          ((edgeCopySourceSectorContainingAndExcludingCopy G A m owner
            selected).card : ℝ)) * base := by
          rw [hcast]
    _ =
        ((edgeCopySourceSectorContainingBothCopies G A m owner selected).card :
          ℝ) * base +
          ((edgeCopySourceSectorContainingAndExcludingCopy G A m owner
            selected).card : ℝ) * base := by
          ring

set_option linter.style.longLine false in

theorem beta_mul_edgeCopySourceSectorContainingCopy_card_mul_eq_both_add_excluding_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ)
    (owner selected : Sharpness.FluxEdgeCopy.Copy G m) (β base : ℝ) :
    β * (((edgeCopySourceSectorContainingCopy G A m owner).card : ℝ) * base) =
      β *
          (((edgeCopySourceSectorContainingBothCopies G A m owner
            selected).card : ℝ) * base) +
        β *
          (((edgeCopySourceSectorContainingAndExcludingCopy G A m owner
            selected).card : ℝ) * base) := by
  rw [
    edgeCopySourceSectorContainingCopy_card_mul_eq_both_add_excluding_mul
      G A m owner selected base]
  ring

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingCopy_card_mul_finset_sum_eq_both_add_excluding_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (Ω : Finset (↥G.edgeFinset → ℕ))
    (owner selected :
      ∀ m : ↥G.edgeFinset → ℕ, Sharpness.FluxEdgeCopy.Copy G m)
    (base : (↥G.edgeFinset → ℕ) → ℝ) :
    (∑ m ∈ Ω,
      ((edgeCopySourceSectorContainingCopy G A m (owner m)).card : ℝ) *
        base m) =
      (∑ m ∈ Ω,
        ((edgeCopySourceSectorContainingBothCopies G A m (owner m)
          (selected m)).card : ℝ) * base m) +
        ∑ m ∈ Ω,
          ((edgeCopySourceSectorContainingAndExcludingCopy G A m (owner m)
            (selected m)).card : ℝ) * base m := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  exact
    edgeCopySourceSectorContainingCopy_card_mul_eq_both_add_excluding_mul
      G A m (owner m) (selected m) (base m)

set_option linter.style.longLine false in

theorem beta_mul_edgeCopySourceSectorContainingCopy_card_mul_finset_sum_eq_both_add_excluding_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (Ω : Finset (↥G.edgeFinset → ℕ))
    (owner selected :
      ∀ m : ↥G.edgeFinset → ℕ, Sharpness.FluxEdgeCopy.Copy G m)
    (β : ℝ) (base : (↥G.edgeFinset → ℕ) → ℝ) :
    β *
        (∑ m ∈ Ω,
          ((edgeCopySourceSectorContainingCopy G A m (owner m)).card : ℝ) *
            base m) =
      β *
          (∑ m ∈ Ω,
            ((edgeCopySourceSectorContainingBothCopies G A m (owner m)
              (selected m)).card : ℝ) * base m) +
        β *
          ∑ m ∈ Ω,
            ((edgeCopySourceSectorContainingAndExcludingCopy G A m (owner m)
              (selected m)).card : ℝ) * base m := by
  rw [
    edgeCopySourceSectorContainingCopy_card_mul_finset_sum_eq_both_add_excluding_mul
      G A Ω owner selected base]
  ring

set_option linter.style.longLine false in

theorem edgeCopySourceSectorContainingCopy_card_mul_finset_sum_beta_mul_eq_both_add_excluding_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (Ω : Finset (↥G.edgeFinset → ℕ))
    (owner selected :
      ∀ m : ↥G.edgeFinset → ℕ, Sharpness.FluxEdgeCopy.Copy G m)
    (β : ℝ) (base : (↥G.edgeFinset → ℕ) → ℝ) :
    (∑ m ∈ Ω,
      β *
        (((edgeCopySourceSectorContainingCopy G A m (owner m)).card : ℝ) *
          base m)) =
      (∑ m ∈ Ω,
        β *
          (((edgeCopySourceSectorContainingBothCopies G A m (owner m)
            (selected m)).card : ℝ) * base m)) +
        ∑ m ∈ Ω,
          β *
            (((edgeCopySourceSectorContainingAndExcludingCopy G A m (owner m)
              (selected m)).card : ℝ) * base m) := by
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  exact
    beta_mul_edgeCopySourceSectorContainingCopy_card_mul_finset_sum_eq_both_add_excluding_mul
      G A Ω owner selected β base

open Classical in


theorem edgeCopySourceSector_card_switching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ)
    {u v : V} (huv : u ≠ v)
    (hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A) :
    (edgeCopySourceSector G (A ∆ ({u, v} : Finset V)) m).card =
      if Sharpness.RandomCurrent.connK
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) u v then
        (edgeCopySourceSector G A m).card
      else
        0 := by
  classical
  simpa [edgeCopySourceSector] using
    Sharpness.RandomCurrent.switching_card
      (Sharpness.FluxEdgeCopy.endsM G m)
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m))
      (fun i _hi => Sharpness.FluxEdgeCopy.endsM_not_isDiag G m i)
      A hfull huv

set_option linter.style.longLine false in

theorem edgeCopySourceSector_card_eq_of_switching_conn
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ)
    {u v : V} (huv : u ≠ v)
    (hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A)
    (hconn :
      Sharpness.RandomCurrent.connK
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) u v) :
    (edgeCopySourceSector G (A ∆ ({u, v} : Finset V)) m).card =
      (edgeCopySourceSector G A m).card := by
  simpa [hconn] using
    edgeCopySourceSector_card_switching
      (G := G) (A := A) (m := m) huv hfull

set_option linter.style.longLine false in

theorem edgeCopySourceSector_card_eq_zero_of_switching_not_conn
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ)
    {u v : V} (huv : u ≠ v)
    (hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A)
    (hnot :
      ¬ Sharpness.RandomCurrent.connK
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) u v) :
    (edgeCopySourceSector G (A ∆ ({u, v} : Finset V)) m).card = 0 := by
  simpa [hnot] using
    edgeCopySourceSector_card_switching
      (G := G) (A := A) (m := m) huv hfull

set_option linter.style.longLine false in


theorem edgeCopy_connK_univ_of_ends_eq_pair
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    {i : Sharpness.FluxEdgeCopy.Copy G m} {a b : V}
    (hab : a ≠ b)
    (hends : Sharpness.FluxEdgeCopy.endsM G m i = s(a, b)) :
    Sharpness.RandomCurrent.connK
      (Sharpness.FluxEdgeCopy.endsM G m)
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) a b := by
  exact Relation.ReflTransGen.single
    ⟨i, Finset.mem_univ i, by rw [hends]; simp,
      by rw [hends]; simp, hab⟩

set_option linter.style.longLine false in


theorem edgeCopy_connK_univ_of_copy_edge_eq_pair
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    {i : Sharpness.FluxEdgeCopy.Copy G m}
    {e0 : ↥G.edgeFinset} {a b : V}
    (hab : a ≠ b)
    (hi : i.1 = e0)
    (hedge : e0.1 = s(a, b)) :
    Sharpness.RandomCurrent.connK
      (Sharpness.FluxEdgeCopy.endsM G m)
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) a b := by
  exact edgeCopy_connK_univ_of_ends_eq_pair
    (G := G) (m := m) (i := i) hab
    (by simp [Sharpness.FluxEdgeCopy.endsM, hi, hedge])

set_option linter.style.longLine false in


theorem fluxEdgeCopy_copy_fintype_card_eq_sum_multiplicity
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) :
    Fintype.card (Sharpness.FluxEdgeCopy.Copy G m) =
      ∑ e : ↥G.edgeFinset, m e := by
  classical
  rw [Fintype.card_sigma]
  simp

set_option linter.style.longLine false in

theorem edgeCopySourceSector_card_le_powerset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) :
    (edgeCopySourceSector G A m).card ≤
      ((Finset.univ :
        Finset (Sharpness.FluxEdgeCopy.Copy G m)).powerset).card := by
  simpa [edgeCopySourceSector] using
    (Finset.card_filter_le
      ((Finset.univ :
        Finset (Sharpness.FluxEdgeCopy.Copy G m)).powerset)
      (fun K =>
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m) K = A))

set_option linter.style.longLine false in


theorem edgeCopySourceSector_card_le_two_pow_copy_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) :
    (edgeCopySourceSector G A m).card ≤
      2 ^ Fintype.card (Sharpness.FluxEdgeCopy.Copy G m) := by
  calc
    (edgeCopySourceSector G A m).card ≤
        ((Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy G m)).powerset).card :=
      edgeCopySourceSector_card_le_powerset_card G A m
    _ = 2 ^ Fintype.card (Sharpness.FluxEdgeCopy.Copy G m) := by
      simp

set_option linter.style.longLine false in


theorem edgeCopySourceSector_card_le_two_pow_sum_multiplicity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) :
    (edgeCopySourceSector G A m).card ≤
      2 ^ (∑ e : ↥G.edgeFinset, m e) := by
  calc
    (edgeCopySourceSector G A m).card ≤
        2 ^ Fintype.card (Sharpness.FluxEdgeCopy.Copy G m) :=
      edgeCopySourceSector_card_le_two_pow_copy_card G A m
    _ = 2 ^ (∑ e : ↥G.edgeFinset, m e) := by
      rw [fluxEdgeCopy_copy_fintype_card_eq_sum_multiplicity]

set_option linter.style.longLine false in

theorem edgeCopySourceSector_card_cast_le_two_pow_sum_multiplicity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) :
    ((edgeCopySourceSector G A m).card : ℝ) ≤
      (2 : ℝ) ^ (∑ e : ↥G.edgeFinset, m e) := by
  exact_mod_cast
    edgeCopySourceSector_card_le_two_pow_sum_multiplicity G A m

set_option linter.style.longLine false in


theorem sum_multiplicity_update_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (∑ e : ↥G.edgeFinset,
      Function.update m e0 (m e0 + 1) e) =
        (∑ e : ↥G.edgeFinset, m e) + 1 := by
  classical
  calc
    (∑ e : ↥G.edgeFinset,
        Function.update m e0 (m e0 + 1) e) =
        ∑ e : ↥G.edgeFinset,
          (m e + if e = e0 then (1 : ℕ) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro e _he
      by_cases he0 : e = e0
      · subst e
        simp [Function.update_self]
      · simp [he0]
    _ = (∑ e : ↥G.edgeFinset, m e) +
          ∑ e : ↥G.edgeFinset,
            (if e = e0 then (1 : ℕ) else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ e : ↥G.edgeFinset, m e) + 1 := by
      have hones :
          (∑ e : ↥G.edgeFinset,
            (if e = e0 then (1 : ℕ) else 0)) = 1 := by
        simp
      rw [hones]

set_option linter.style.longLine false in


theorem edgeCopySourceSector_card_update_succ_le_two_pow_sum_multiplicity_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (edgeCopySourceSector G A
      (Function.update m e0 (m e0 + 1))).card ≤
      2 ^ ((∑ e : ↥G.edgeFinset, m e) + 1) := by
  calc
    (edgeCopySourceSector G A
        (Function.update m e0 (m e0 + 1))).card ≤
        2 ^ (∑ e : ↥G.edgeFinset,
          Function.update m e0 (m e0 + 1) e) :=
      edgeCopySourceSector_card_le_two_pow_sum_multiplicity G A
        (Function.update m e0 (m e0 + 1))
    _ = 2 ^ ((∑ e : ↥G.edgeFinset, m e) + 1) := by
      rw [sum_multiplicity_update_succ]

set_option linter.style.longLine false in

theorem edgeCopySourceSector_card_cast_update_succ_le_two_pow_sum_multiplicity_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    ((edgeCopySourceSector G A
      (Function.update m e0 (m e0 + 1))).card : ℝ) ≤
      (2 : ℝ) ^ ((∑ e : ↥G.edgeFinset, m e) + 1) := by
  exact_mod_cast
    edgeCopySourceSector_card_update_succ_le_two_pow_sum_multiplicity_add_one
      G A m e0


theorem randomCurrent_sources_insert_singleton
    {ι V : Type*} [DecidableEq ι] [Finite ι] [Fintype V] [DecidableEq V]
    (ends : ι → Sym2 V) {K : Finset ι} {i : ι}
    (hiK : i ∉ K) :
    Sharpness.RandomCurrent.sources ends (insert i K) =
      Sharpness.RandomCurrent.sources ends K ∆
        Sharpness.RandomCurrent.sources ends ({i} : Finset ι) := by
  classical
  letI := Fintype.ofFinite ι
  have hinsert : insert i K = K ∆ ({i} : Finset ι) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [hiK, Finset.mem_symmDiff]
    · simp [hji, Finset.mem_symmDiff]
  rw [hinsert, Sharpness.RandomCurrent.sources_symmDiff]


theorem randomCurrent_sources_insert_singleton_of_ends_eq
    {ι V : Type*} [DecidableEq ι] [Finite ι] [Fintype V] [DecidableEq V]
    (ends : ι → Sym2 V) {K : Finset ι} {i : ι}
    {A : Finset V} {a b : V}
    (hiK : i ∉ K)
    (hsrc : Sharpness.RandomCurrent.sources ends K = A)
    (hends : ends i = s(a, b)) :
    Sharpness.RandomCurrent.sources ends (insert i K) =
      A ∆ ({a, b} : Finset V) := by
  letI := Fintype.ofFinite ι
  rw [randomCurrent_sources_insert_singleton ends hiK, hsrc]
  have hsingle :
      Sharpness.RandomCurrent.sources ends ({i} : Finset ι) =
        {a, b} := by
    ext x
    rw [Sharpness.RandomCurrent.mem_sources]
    unfold Sharpness.RandomCurrent.degK
    rw [Finset.filter_singleton]
    rw [hends]
    by_cases hx : x ∈ (s(a, b) : Sym2 V)
    · rw [if_pos hx]
      simp only [Finset.card_singleton]
      rw [show Odd 1 ↔ True by simp]
      simp only [true_iff]
      simpa [Sym2.mem_iff] using hx
    · rw [if_neg hx]
      simp only [Finset.card_empty]
      rw [show Odd 0 ↔ False by simp]
      simp only [false_iff]
      simpa [Sym2.mem_iff] using hx
  rw [hsingle]


theorem randomCurrent_sources_univ_sdiff
    {ι V : Type*} [DecidableEq ι] [Fintype ι] [Fintype V] [DecidableEq V]
    (ends : ι → Sym2 V) (K : Finset ι) :
    Sharpness.RandomCurrent.sources ends ((Finset.univ : Finset ι) \ K) =
      Sharpness.RandomCurrent.sources ends (Finset.univ : Finset ι) ∆
        Sharpness.RandomCurrent.sources ends K := by
  have hset :
      ((Finset.univ : Finset ι) \ K) =
        (Finset.univ : Finset ι) ∆ K := by
    ext i
    simp [Finset.mem_symmDiff]
  rw [hset, Sharpness.RandomCurrent.sources_symmDiff]

set_option linter.style.longLine false in


theorem edgeCopyFullSources_eq_sources_ofEdgeFun
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
      Sharpness.sources G (Sharpness.ofEdgeFun G m) := by
  rw [Sharpness.FluxEdgeCopy.sources_eq,
    Sharpness.FluxEdgeCopy.profileFlux_univ]

set_option linter.style.longLine false in


theorem finset_symmDiff_left_cancel_self
    {α : Type*} [DecidableEq α] (C A : Finset α) :
    C ∆ (C ∆ A) = A := by
  ext x
  by_cases hxA : x ∈ A
  · simp [hxA]
  · simp [hxA]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorExcludingCopy_univ_sdiff_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A C : Finset V} {m : ↥G.edgeFinset → ℕ}
    {i : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
        C)
    (hK : K ∈ edgeCopySourceSectorExcludingCopy G A m i) :
    ((Finset.univ :
        Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ K) ∈
      edgeCopySourceSectorContainingCopy G (C ∆ A) m i := by
  classical
  rcases
      (mem_edgeCopySourceSectorExcludingCopy
        (G := G) (A := A) (m := m) (i := i) (K := K)).mp hK with
    ⟨hKsource, hi_not_mem⟩
  have hsrcK :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m) K =
        A :=
    (mem_edgeCopySourceSector
      (G := G) (A := A) (m := m) (K := K)).mp hKsource
  have hsrcCompl :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          ((Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ K) =
        C ∆ A := by
    rw [randomCurrent_sources_univ_sdiff, hfull, hsrcK]
  exact
    (mem_edgeCopySourceSectorContainingCopy
      (G := G) (A := C ∆ A) (m := m) (i := i)
      (K :=
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ K)).mpr
      ⟨(mem_edgeCopySourceSector
          (G := G) (A := C ∆ A) (m := m)
          (K :=
            (Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ K)).mpr
          hsrcCompl,
        by simp [hi_not_mem]⟩

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingCopy_univ_sdiff_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A C : Finset V} {m : ↥G.edgeFinset → ℕ}
    {i : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
        C)
    (hK : K ∈ edgeCopySourceSectorContainingCopy G A m i) :
    ((Finset.univ :
        Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ K) ∈
      edgeCopySourceSectorExcludingCopy G (C ∆ A) m i := by
  classical
  rcases
      (mem_edgeCopySourceSectorContainingCopy
        (G := G) (A := A) (m := m) (i := i) (K := K)).mp hK with
    ⟨hKsource, hi_mem⟩
  have hsrcK :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m) K =
        A :=
    (mem_edgeCopySourceSector
      (G := G) (A := A) (m := m) (K := K)).mp hKsource
  have hsrcCompl :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          ((Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ K) =
        C ∆ A := by
    rw [randomCurrent_sources_univ_sdiff, hfull, hsrcK]
  exact
    (mem_edgeCopySourceSectorExcludingCopy
      (G := G) (A := C ∆ A) (m := m) (i := i)
      (K :=
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ K)).mpr
      ⟨(mem_edgeCopySourceSector
          (G := G) (A := C ∆ A) (m := m)
          (K :=
            (Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ K)).mpr
          hsrcCompl,
        by simp [hi_mem]⟩

set_option linter.style.longLine false in


theorem edgeCopySourceSectorExcludingCopy_univ_sdiff_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A C : Finset V} {m : ↥G.edgeFinset → ℕ}
    {i : Sharpness.FluxEdgeCopy.Copy G m}
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
        C) :
    (edgeCopySourceSectorExcludingCopy G A m i).card =
      (edgeCopySourceSectorContainingCopy G (C ∆ A) m i).card := by
  classical
  let Copy := Sharpness.FluxEdgeCopy.Copy G m
  let left := edgeCopySourceSectorExcludingCopy G A m i
  let right := edgeCopySourceSectorContainingCopy G (C ∆ A) m i
  have hcompl_inj :
      Function.Injective
        (fun K : Finset Copy => (Finset.univ : Finset Copy) \ K) := by
    intro K L hKL
    ext x
    have hmem := congrArg (fun S : Finset Copy => x ∈ S) hKL
    have hnot : x ∉ K ↔ x ∉ L := by
      simpa using hmem
    constructor
    · intro hxK
      by_contra hxL
      exact (hnot.mpr hxL) hxK
    · intro hxL
      by_contra hxK
      exact (hnot.mp hxK) hxL
  have hle_left : left.card ≤ right.card := by
    refine
      Finset.card_le_card_of_injOn
        (fun K : Finset Copy => (Finset.univ : Finset Copy) \ K) ?_ ?_
    · intro K hK
      simpa [left, right, Copy] using
        edgeCopySourceSectorExcludingCopy_univ_sdiff_mem
          (G := G) (A := A) (C := C) (m := m) (i := i) (K := K)
          hfull hK
    · intro K _hK L _hL hKL
      exact hcompl_inj hKL
  have hle_right : right.card ≤ left.card := by
    refine
      Finset.card_le_card_of_injOn
        (fun K : Finset Copy => (Finset.univ : Finset Copy) \ K) ?_ ?_
    · intro K hK
      have hmem :
          ((Finset.univ : Finset Copy) \ K) ∈
            edgeCopySourceSectorExcludingCopy G (C ∆ (C ∆ A)) m i := by
        simpa [right, Copy] using
          edgeCopySourceSectorContainingCopy_univ_sdiff_mem
            (G := G) (A := C ∆ A) (C := C) (m := m) (i := i)
            (K := K) hfull hK
      simpa [left, Copy, finset_symmDiff_left_cancel_self C A] using hmem
    · intro K _hK L _hL hKL
      exact hcompl_inj hKL
  exact le_antisymm hle_left hle_right

set_option linter.style.longLine false in


theorem edgeCopySourceSectorExcludingCopy_card_pos_iff_containingCopy_card_pos_of_univ_source
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A C : Finset V} {m : ↥G.edgeFinset → ℕ}
    {i : Sharpness.FluxEdgeCopy.Copy G m}
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
        C) :
    0 < (edgeCopySourceSectorExcludingCopy G A m i).card ↔
      0 < (edgeCopySourceSectorContainingCopy G (C ∆ A) m i).card := by
  rw [edgeCopySourceSectorExcludingCopy_univ_sdiff_card_eq hfull]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A C : Finset V} {m : ↥G.edgeFinset → ℕ}
    {inside outside : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
        C)
    (hK :
      K ∈ edgeCopySourceSectorContainingAndExcludingCopy G A m inside outside) :
    ((Finset.univ :
        Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ K) ∈
      edgeCopySourceSectorContainingAndExcludingCopy G (C ∆ A) m outside
        inside := by
  classical
  rcases
      (mem_edgeCopySourceSectorContainingAndExcludingCopy
        (G := G) (A := A) (m := m) (inside := inside)
        (outside := outside) (K := K)).mp hK with
    ⟨hKsource, hinside, houtside⟩
  have hsrcK :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m) K =
        A :=
    (mem_edgeCopySourceSector
      (G := G) (A := A) (m := m) (K := K)).mp hKsource
  have hsrcCompl :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          ((Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ K) =
        C ∆ A := by
    rw [randomCurrent_sources_univ_sdiff, hfull, hsrcK]
  exact
    (mem_edgeCopySourceSectorContainingAndExcludingCopy
      (G := G) (A := C ∆ A) (m := m) (inside := outside)
      (outside := inside)
      (K :=
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ K)).mpr
      ⟨(mem_edgeCopySourceSector
          (G := G) (A := C ∆ A) (m := m)
          (K :=
            (Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ K)).mpr
          hsrcCompl,
        by simp [houtside],
        by simp [hinside]⟩

set_option linter.style.longLine false in

theorem finset_univ_sdiff_injective
    {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Injective
      (fun K : Finset α => (Finset.univ : Finset α) \ K) := by
  intro K L hKL
  ext x
  have hmem := congrArg (fun S : Finset α => x ∈ S) hKL
  have hnot : x ∉ K ↔ x ∉ L := by
    simpa using hmem
  constructor
  · intro hxK
    by_contra hxL
    exact (hnot.mpr hxL) hxK
  · intro hxL
    by_contra hxK
    exact (hnot.mp hxK) hxL

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A C : Finset V} {m : ↥G.edgeFinset → ℕ}
    {inside outside : Sharpness.FluxEdgeCopy.Copy G m}
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
        C) :
    (edgeCopySourceSectorContainingAndExcludingCopy G A m inside outside).card =
      (edgeCopySourceSectorContainingAndExcludingCopy G (C ∆ A) m outside
        inside).card := by
  classical
  let Copy := Sharpness.FluxEdgeCopy.Copy G m
  let left := edgeCopySourceSectorContainingAndExcludingCopy G A m inside outside
  let right :=
    edgeCopySourceSectorContainingAndExcludingCopy G (C ∆ A) m outside inside
  have hle_left : left.card ≤ right.card := by
    refine
      Finset.card_le_card_of_injOn
        (fun K : Finset Copy => (Finset.univ : Finset Copy) \ K) ?_ ?_
    · intro K hK
      simpa [left, right, Copy] using
        edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_mem
          (G := G) (A := A) (C := C) (m := m) (inside := inside)
          (outside := outside) (K := K) hfull hK
    · intro K _hK L _hL hKL
      exact finset_univ_sdiff_injective hKL
  have hle_right : right.card ≤ left.card := by
    refine
      Finset.card_le_card_of_injOn
        (fun K : Finset Copy => (Finset.univ : Finset Copy) \ K) ?_ ?_
    · intro K hK
      have hmem :
          ((Finset.univ : Finset Copy) \ K) ∈
            edgeCopySourceSectorContainingAndExcludingCopy G (C ∆ (C ∆ A)) m
              inside outside := by
        simpa [right, Copy] using
          edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_mem
            (G := G) (A := C ∆ A) (C := C) (m := m)
            (inside := outside) (outside := inside) (K := K) hfull hK
      simpa [left, finset_symmDiff_left_cancel_self] using hmem
    · intro K _hK L _hL hKL
      exact finset_univ_sdiff_injective hKL
  exact le_antisymm hle_left hle_right

set_option linter.style.longLine false in

theorem edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_card_mul_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A C : Finset V} {m : ↥G.edgeFinset → ℕ}
    {inside outside : Sharpness.FluxEdgeCopy.Copy G m}
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
        C)
    (base : ℝ) :
    ((edgeCopySourceSectorContainingAndExcludingCopy G A m inside outside).card :
        ℝ) * base =
      ((edgeCopySourceSectorContainingAndExcludingCopy G (C ∆ A) m outside
          inside).card : ℝ) * base := by
  rw [
    edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_card_eq
      (G := G) (A := A) (C := C) (m := m) (inside := inside)
      (outside := outside) hfull]

set_option linter.style.longLine false in

theorem beta_mul_edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_card_mul_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A C : Finset V} {m : ↥G.edgeFinset → ℕ}
    {inside outside : Sharpness.FluxEdgeCopy.Copy G m}
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
        C)
    (β base : ℝ) :
    β *
        (((edgeCopySourceSectorContainingAndExcludingCopy G A m inside
          outside).card : ℝ) * base) =
      β *
        (((edgeCopySourceSectorContainingAndExcludingCopy G (C ∆ A) m outside
          inside).card : ℝ) * base) := by
  rw [
    edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_card_mul_eq
      (G := G) (A := A) (C := C) (m := m) (inside := inside)
      (outside := outside) hfull base]

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_sources_ofEdgeFun_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {inside outside : Sharpness.FluxEdgeCopy.Copy G m}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hK :
      K ∈ edgeCopySourceSectorContainingAndExcludingCopy G A m inside outside) :
    ((Finset.univ :
        Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ K) ∈
      edgeCopySourceSectorContainingAndExcludingCopy G
        (Sharpness.sources G (Sharpness.ofEdgeFun G m) ∆ A) m outside
        inside := by
  exact
    edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_mem
      (G := G) (A := A)
      (C := Sharpness.sources G (Sharpness.ofEdgeFun G m)) (m := m)
      (inside := inside) (outside := outside) (K := K)
      (edgeCopyFullSources_eq_sources_ofEdgeFun G m) hK

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_sources_ofEdgeFun_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {inside outside : Sharpness.FluxEdgeCopy.Copy G m} :
    (edgeCopySourceSectorContainingAndExcludingCopy G A m inside outside).card =
      (edgeCopySourceSectorContainingAndExcludingCopy G
        (Sharpness.sources G (Sharpness.ofEdgeFun G m) ∆ A) m outside
        inside).card := by
  exact
    edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_card_eq
      (G := G) (A := A)
      (C := Sharpness.sources G (Sharpness.ofEdgeFun G m)) (m := m)
      (inside := inside) (outside := outside)
      (edgeCopyFullSources_eq_sources_ofEdgeFun G m)

set_option linter.style.longLine false in


theorem edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_sources_ofEdgeFun_card_mul_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {inside outside : Sharpness.FluxEdgeCopy.Copy G m}
    (base : ℝ) :
    ((edgeCopySourceSectorContainingAndExcludingCopy G A m inside outside).card :
        ℝ) * base =
      ((edgeCopySourceSectorContainingAndExcludingCopy G
        (Sharpness.sources G (Sharpness.ofEdgeFun G m) ∆ A) m outside
        inside).card : ℝ) * base := by
  rw [
    edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_sources_ofEdgeFun_card_eq
      (G := G) (A := A) (m := m) (inside := inside)
      (outside := outside)]

set_option linter.style.longLine false in


theorem beta_mul_edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_sources_ofEdgeFun_card_mul_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {m : ↥G.edgeFinset → ℕ}
    {inside outside : Sharpness.FluxEdgeCopy.Copy G m}
    (β base : ℝ) :
    β *
        (((edgeCopySourceSectorContainingAndExcludingCopy G A m inside
          outside).card : ℝ) * base) =
      β *
        (((edgeCopySourceSectorContainingAndExcludingCopy G
          (Sharpness.sources G (Sharpness.ofEdgeFun G m) ∆ A) m outside
          inside).card : ℝ) * base) := by
  rw [
    edgeCopySourceSectorContainingAndExcludingCopy_univ_sdiff_sources_ofEdgeFun_card_mul_eq
      (G := G) (A := A) (m := m) (inside := inside)
      (outside := outside) base]

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
theorem randomCurrent_sources_empty
    {ι V : Type*} [DecidableEq ι] [Fintype ι] [Fintype V] [DecidableEq V]
    (ends : ι → Sym2 V) :
    Sharpness.RandomCurrent.sources ends (∅ : Finset ι) =
      (∅ : Finset V) := by
  ext x
  rw [Sharpness.RandomCurrent.mem_sources]
  simp [Sharpness.RandomCurrent.degK]

set_option linter.style.longLine false in


theorem randomCurrent_not_mem_sources_of_forall_not_mem_ends
    {ι V : Type*} [Fintype V] [DecidableEq V]
    (ends : ι → Sym2 V) (K : Finset ι) (x : V)
    (h : ∀ i ∈ K, x ∉ ends i) :
    x ∉ Sharpness.RandomCurrent.sources ends K := by
  intro hxsrc
  have hfilter : K.filter (fun i => x ∈ ends i) = ∅ := by
    ext i
    constructor
    · intro hi
      exact False.elim (h i (Finset.mem_filter.mp hi).1
        (Finset.mem_filter.mp hi).2)
    · intro hi
      simp at hi
  simp [Sharpness.RandomCurrent.sources, Sharpness.RandomCurrent.degK,
    hfilter] at hxsrc


theorem finset_singleton_symmDiff_pair_cancel_left
    {α : Type*} [DecidableEq α] {o v w : α}
    (hov : o ≠ v) (how : o ≠ w) (hvw : v ≠ w) :
    ((({o} : Finset α) ∆ ({v} : Finset α)) ∆ ({v, w} : Finset α)) =
      (({o} : Finset α) ∆ ({w} : Finset α)) := by
  ext x
  by_cases hxo : x = o
  · subst x
    simp [Finset.mem_symmDiff, hov, how]
  · by_cases hxv : x = v
    · subst x
      simp [Finset.mem_symmDiff, hxo, hvw]
    · by_cases hxw : x = w
      · subst x
        simp [Finset.mem_symmDiff, hxo, hxv]
      · simp [Finset.mem_symmDiff, hxo, hxv, hxw]


theorem doubledBoxOriginToInnerEndpointSource_symmDiff_innerPair_eq
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    doubledBoxOriginToInnerEndpointSource n v ∆
        ({FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w} :
          Finset (FK.boxVerts 3 (2 * n))) =
      doubledBoxOriginToInnerEndpointSource n w := by
  simpa [doubledBoxOriginToInnerEndpointSource] using
    finset_singleton_symmDiff_pair_cancel_left
      (o := IsingFK.boxOrigin 3 (2 * n))
      (v := FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
      (w := FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
      hov how hvw


theorem doubledBoxOriginToInnerEndpointSource_symmDiff_innerPair_eq_left
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    doubledBoxOriginToInnerEndpointSource n w ∆
        doubledBoxInnerPairSource n v w =
      doubledBoxOriginToInnerEndpointSource n v := by
  have h :=
    doubledBoxOriginToInnerEndpointSource_symmDiff_innerPair_eq
      (n := n) (v := w) (w := v) how hov hvw.symm
  simpa [doubledBoxInnerPairSource, Finset.pair_comm] using h


theorem doubledBoxOriginToInnerEndpointSource_symmDiff_source_eq_innerPair
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    doubledBoxOriginToInnerEndpointSource n v ∆
        doubledBoxOriginToInnerEndpointSource n w =
      doubledBoxInnerPairSource n v w := by
  ext x
  let o := IsingFK.boxOrigin 3 (2 * n)
  let vv := FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v
  let ww := FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w
  by_cases hxo : x = o
  · subst x
    simp [doubledBoxOriginToInnerEndpointSource, doubledBoxInnerPairSource,
      Finset.mem_symmDiff, o, hov, how]
  · by_cases hxv : x = vv
    · subst x
      simp [doubledBoxOriginToInnerEndpointSource, doubledBoxInnerPairSource,
        Finset.mem_symmDiff, o, vv, hxo, hvw]
    · by_cases hxw : x = ww
      · subst x
        simp [doubledBoxOriginToInnerEndpointSource, doubledBoxInnerPairSource,
          Finset.mem_symmDiff, o, vv, ww, hxo, hxv]
      · simp [doubledBoxOriginToInnerEndpointSource, doubledBoxInnerPairSource,
          Finset.mem_symmDiff, o, vv, ww, hxo, hxv, hxw]

open Classical in


theorem doubledBoxOriginToInnerEndpointSourceSector_card_switching
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n v)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card =
      if Sharpness.RandomCurrent.connK
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) then
        (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v) m).card
      else
        0 := by
  have hswitch :=
    edgeCopySourceSector_card_switching
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (m := m)
      (u := FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
      (v := FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
      hvw hfull
  simpa [doubledBoxOriginToInnerEndpointSource_symmDiff_innerPair_eq
    (n := n) (v := v) (w := w) hov how hvw] using hswitch

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourceSector_card_eq_of_switching_conn
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n v)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hconn :
      Sharpness.RandomCurrent.connK
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card =
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m).card := by
  classical
  simpa [hconn] using
    doubledBoxOriginToInnerEndpointSourceSector_card_switching
      (n := n) (v := v) (w := w) m hfull hov how hvw

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourceSector_card_eq_zero_of_switching_not_conn
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n v)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hnot :
      ¬ Sharpness.RandomCurrent.connK
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card = 0 := by
  classical
  simpa [hnot] using
    doubledBoxOriginToInnerEndpointSourceSector_card_switching
      (n := n) (v := v) (w := w) m hfull hov how hvw

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourceSector_reverse_card_eq_of_switching_conn
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hconn :
      Sharpness.RandomCurrent.connK
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m).card =
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card := by
  exact
    doubledBoxOriginToInnerEndpointSourceSector_card_eq_of_switching_conn
      (n := n) (v := w) (w := v) m hfull how hov hvw.symm
      (Sharpness.RandomCurrent.connK_symm
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m))
        hconn)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourceSector_reverse_card_eq_zero_of_switching_not_conn
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hnot :
      ¬ Sharpness.RandomCurrent.connK
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v) m).card = 0 := by
  have hnot_symm :
      ¬ Sharpness.RandomCurrent.connK
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) := by
    intro hconn_symm
    exact hnot
      (Sharpness.RandomCurrent.connK_symm
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m))
        hconn_symm)
  exact
    doubledBoxOriginToInnerEndpointSourceSector_card_eq_zero_of_switching_not_conn
      (n := n) (v := w) (w := v) m hfull how hov hvw.symm hnot_symm


theorem doubledBox_sources_remove_innerPairCopy
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m))
    {i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m}
    (hiK : i ∈ K)
    (hsrc :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) K =
        doubledBoxOriginToInnerEndpointSource n w)
    (hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) (K \ {i}) =
      doubledBoxOriginToInnerEndpointSource n v := by
  rw [randomCurrent_sources_sdiff_singleton
    (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) hiK, hsrc]
  have hsingle :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          ({i} :
            Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxInnerPairSource n v w := by
    simpa [doubledBoxInnerPairSource] using
      randomCurrent_sources_singleton_of_ends_eq
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) hends
  rw [hsingle]
  exact doubledBoxOriginToInnerEndpointSource_symmDiff_innerPair_eq_left
    hov how hvw


theorem doubledBox_sources_preimageErase_innerPairCopy
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m))
    {i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m}
    (hiK : i ∈ K)
    (hsrc :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) K =
        doubledBoxOriginToInnerEndpointSource n w)
    (hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
          (Function.update m i.1 (m i.1 - 1)))
        (copyDeletePreimageDecrementEraseFinset (FK.boxGraph 3 (2 * n))
          m i K) =
      doubledBoxOriginToInnerEndpointSource n v := by
  rw [copyDeletePreimageDecrementErase_sources]
  have hold :=
    doubledBox_sources_remove_innerPairCopy
      (n := n) (v := v) (w := w) m K hiK hsrc hends hov how hvw
  simpa [Finset.sdiff_singleton_eq_erase] using hold


theorem doubledBox_sources_univ_preimageErase_innerPairCopy
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
          (Function.update m i.1 (m i.1 - 1)))
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
            (Function.update m i.1 (m i.1 - 1)))) =
      doubledBoxOriginToInnerEndpointSource n v := by
  have htransport :=
    copyDeletePreimageDecrementErase_sources (FK.boxGraph 3 (2 * n)) m i
      (Finset.univ :
        Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m))
  rw [copyDeletePreimageDecrementEraseFinset_univ] at htransport
  rw [htransport]
  have hold :=
    doubledBox_sources_remove_innerPairCopy
      (n := n) (v := v) (w := w) m
      (Finset.univ :
        Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m))
      (Finset.mem_univ i) hfull hends hov how hvw
  simpa [Finset.sdiff_singleton_eq_erase] using hold


theorem doubledBox_sources_preimageErase_of_not_mem
    {n : ℕ} {w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m))
    {i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m}
    (hiK : i ∉ K)
    (hsrc :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) K =
        doubledBoxOriginToInnerEndpointSource n w) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
          (Function.update m i.1 (m i.1 - 1)))
        (copyDeletePreimageDecrementEraseFinset (FK.boxGraph 3 (2 * n))
          m i K) =
      doubledBoxOriginToInnerEndpointSource n w := by
  rw [copyDeletePreimageDecrementErase_sources]
  have herase : K.erase i = K := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [hiK]
    · simp [Finset.mem_erase, hji]
  simpa [herase] using hsrc

set_option linter.style.longLine false in


theorem copyDeletePreimageDecrementErase_sources_of_not_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy G m))
    {i : Sharpness.FluxEdgeCopy.Copy G m}
    (hiK : i ∉ K) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G
          (Function.update m i.1 (m i.1 - 1)))
        (copyDeletePreimageDecrementEraseFinset G m i K) =
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m) K := by
  rw [copyDeletePreimageDecrementErase_sources]
  have herase : K.erase i = K := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [hiK]
    · simp [Finset.mem_erase, hji]
  simp [herase]


theorem doubledBox_sources_complement_preimageErase_of_not_mem_innerPairCopy
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m))
    {i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m}
    (hiK : i ∉ K)
    (hsrc :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) K =
        doubledBoxOriginToInnerEndpointSource n w)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
          (Function.update m i.1 (m i.1 - 1)))
        ((Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
              (Function.update m i.1 (m i.1 - 1)))) \
          copyDeletePreimageDecrementEraseFinset (FK.boxGraph 3 (2 * n))
            m i K) =
      doubledBoxInnerPairSource n v w := by
  rw [randomCurrent_sources_univ_sdiff]
  rw [doubledBox_sources_univ_preimageErase_innerPairCopy
    (n := n) (v := v) (w := w) m i hfull hends hov how hvw]
  rw [doubledBox_sources_preimageErase_of_not_mem
    (n := n) (w := w) m K hiK hsrc]
  exact doubledBoxOriginToInnerEndpointSource_symmDiff_source_eq_innerPair
    hov how hvw

set_option linter.style.longLine false in


theorem doubledBox_sources_complement_preimageErase_of_not_mem_innerPairSource
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m))
    {i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m}
    (hiK : i ∉ K)
    (hsrc :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) K =
        doubledBoxInnerPairSource n v w)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
          (Function.update m i.1 (m i.1 - 1)))
        ((Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
              (Function.update m i.1 (m i.1 - 1)))) \
          copyDeletePreimageDecrementEraseFinset (FK.boxGraph 3 (2 * n))
            m i K) =
      doubledBoxOriginToInnerEndpointSource n w := by
  rw [randomCurrent_sources_univ_sdiff]
  rw [doubledBox_sources_univ_preimageErase_innerPairCopy
    (n := n) (v := v) (w := w) m i hfull hends hov how hvw]
  rw [copyDeletePreimageDecrementErase_sources_of_not_mem
    (G := FK.boxGraph 3 (2 * n)) m K hiK]
  rw [hsrc]
  exact doubledBoxOriginToInnerEndpointSource_symmDiff_innerPair_eq
    hov how hvw


theorem doubledBox_sources_complement_preimageErase_of_not_mem_switched_empty
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m))
    {i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m}
    (hiK : i ∉ K)
    (hsrc :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) K =
        doubledBoxOriginToInnerEndpointSource n v)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
          (Function.update m i.1 (m i.1 - 1)))
        ((Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
              (Function.update m i.1 (m i.1 - 1)))) \
          copyDeletePreimageDecrementEraseFinset (FK.boxGraph 3 (2 * n))
            m i K) =
      (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
  rw [randomCurrent_sources_univ_sdiff]
  rw [doubledBox_sources_univ_preimageErase_innerPairCopy
    (n := n) (v := v) (w := w) m i hfull hends hov how hvw]
  rw [doubledBox_sources_preimageErase_of_not_mem
    (n := n) (w := v) m K hiK hsrc]
  simp


theorem doubledBox_sources_complement_preimageErase_innerPairCopy
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m))
    {i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m}
    (hiK : i ∈ K)
    (hsrc :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) K =
        doubledBoxOriginToInnerEndpointSource n w)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
          (Function.update m i.1 (m i.1 - 1)))
        ((Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
              (Function.update m i.1 (m i.1 - 1)))) \
          copyDeletePreimageDecrementEraseFinset (FK.boxGraph 3 (2 * n))
            m i K) =
      (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
  rw [randomCurrent_sources_univ_sdiff]
  rw [doubledBox_sources_univ_preimageErase_innerPairCopy
    (n := n) (v := v) (w := w) m i hfull hends hov how hvw]
  rw [doubledBox_sources_preimageErase_innerPairCopy
    (n := n) (v := v) (w := w) m K hiK hsrc hends hov how hvw]
  simp


theorem doubledBox_sources_preimageErase_innerPairCopy_switched
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m))
    {i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m}
    (hiK : i ∈ K)
    (hsrc :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) K =
        doubledBoxOriginToInnerEndpointSource n v)
    (hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
          (Function.update m i.1 (m i.1 - 1)))
        (copyDeletePreimageDecrementEraseFinset (FK.boxGraph 3 (2 * n))
          m i K) =
      doubledBoxOriginToInnerEndpointSource n w := by
  have hends_swap :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) := by
    rw [hends, Sym2.eq_swap]
  exact
    doubledBox_sources_preimageErase_innerPairCopy
      (n := n) (v := w) (w := v) m K hiK hsrc hends_swap how hov
      hvw.symm


theorem doubledBox_sources_complement_preimageErase_innerPairCopy_switched_innerPair
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m))
    {i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m}
    (hiK : i ∈ K)
    (hsrc :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) K =
        doubledBoxOriginToInnerEndpointSource n v)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
          (Function.update m i.1 (m i.1 - 1)))
        ((Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n))
              (Function.update m i.1 (m i.1 - 1)))) \
          copyDeletePreimageDecrementEraseFinset (FK.boxGraph 3 (2 * n))
            m i K) =
      doubledBoxInnerPairSource n v w := by
  rw [randomCurrent_sources_univ_sdiff]
  rw [doubledBox_sources_univ_preimageErase_innerPairCopy
    (n := n) (v := v) (w := w) m i hfull hends hov how hvw]
  rw [doubledBox_sources_preimageErase_innerPairCopy_switched
    (n := n) (v := v) (w := w) m K hiK hsrc hends hov how hvw]
  exact doubledBoxOriginToInnerEndpointSource_symmDiff_source_eq_innerPair
    hov how hvw


end Exact3D
end StatMech
