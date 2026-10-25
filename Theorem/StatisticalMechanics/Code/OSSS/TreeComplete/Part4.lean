/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part7
import Def.StatisticalMechanics.Code.OSSS.TreeComplete.Part3
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace TreeComplete

open StatMech.OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open StatMech.OSSS.RevealmentConstruction

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]

omit [Fintype E] [DecidableEq E] in

theorem runState_repeatList (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (n : ℕ) (disc : Finset V) :
    runState (geomGuard endU endV) (geomStep endU endV) ω (repeatList l n) disc
      = (fun D => runState (geomGuard endU endV) (geomStep endU endV) ω l D)^[n] disc := by
  induction n generalizing disc with
  | zero => simp [repeatList, runState]
  | succ k ih =>
      rw [repeatList, runState_append, Function.iterate_succ, Function.comp_apply]
      exact ih _


theorem fixpoint_iterate_card {V : Type*} [DecidableEq V]
    (f : Finset V → Finset V) (U : Finset V)
    (hinfl : ∀ D, D ⊆ f D) (hbound : ∀ D, D ⊆ U → f D ⊆ U)
    (D₀ : Finset V) (hD₀ : D₀ ⊆ U) :
    f (f^[U.card] D₀) = f^[U.card] D₀ := by
  have hiter_sub : ∀ n, f^[n] D₀ ⊆ U := by
    intro n; induction n with
    | zero => simpa using hD₀
    | succ k ih => rw [Function.iterate_succ', Function.comp_apply]; exact hbound _ ih
  have habsorb : ∀ k m, f (f^[k] D₀) = f^[k] D₀ → f^[k + m] D₀ = f^[k] D₀ := by
    intro k m hk
    induction m with
    | zero => rfl
    | succ j ih =>
      have hstep : f^[k + (j + 1)] D₀ = f (f^[k + j] D₀) := by
        rw [show k + (j + 1) = (k + j) + 1 from by ring, Function.iterate_succ',
          Function.comp_apply]
      rw [hstep, ih, hk]
  by_contra hcon
  have hnofix : ∀ k, k ≤ U.card → f (f^[k] D₀) ≠ f^[k] D₀ := by
    intro k hk hfk
    apply hcon
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hk
    rw [hm, habsorb k m hfk, hfk]
  have hstrict : ∀ k, k < U.card → (f^[k] D₀).card < (f^[k + 1] D₀).card := by
    intro k hk
    have hne := hnofix k (le_of_lt hk)
    have heq : f^[k + 1] D₀ = f (f^[k] D₀) := by
      rw [Function.iterate_succ', Function.comp_apply]
    rw [heq]
    exact Finset.card_lt_card (lt_of_le_of_ne (hinfl _) (fun h => hne h.symm))
  have hge : ∀ k, k ≤ U.card → k ≤ (f^[k] D₀).card := by
    intro k hk; induction k with
    | zero => exact Nat.zero_le _
    | succ j ih =>
        exact Nat.lt_of_le_of_lt (ih (le_of_lt (Nat.lt_of_succ_le hk)))
          (hstrict j (Nat.lt_of_succ_le hk))
  have hne := hnofix U.card le_rfl
  have heq : f^[U.card + 1] D₀ = f (f^[U.card] D₀) := by
    rw [Function.iterate_succ', Function.comp_apply]
  have hstr : (f^[U.card] D₀).card < (f^[U.card + 1] D₀).card := by
    rw [heq]; exact Finset.card_lt_card (lt_of_le_of_ne (hinfl _) (fun h => hne h.symm))
  have h1 : U.card ≤ (f^[U.card] D₀).card := hge _ le_rfl
  have hle : (f^[U.card + 1] D₀).card ≤ U.card := Finset.card_le_card (hiter_sub _)
  omega


omit [Fintype E] in


theorem runState_repeatList_saturated (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (disc₀ : Finset V) :
    Saturated endU endV ω l
      (runState (geomGuard endU endV) (geomStep endU endV) ω
        (repeatList l (disc₀ ∪ endpointsFinset endU endV l).card) disc₀) := by
  set U := disc₀ ∪ endpointsFinset endU endV l with hU
  set pass := fun D => runState (geomGuard endU endV) (geomStep endU endV) ω l D with hpass
  have hinfl : ∀ D, D ⊆ pass D := fun D => subset_runState endU endV ω l D
  have hbound : ∀ D, D ⊆ U → pass D ⊆ U := by
    intro D hD
    refine subset_trans (runState_subset_union endU endV ω l D) ?_
    rw [hU]
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hd | hep
    · exact hD hd
    · exact Finset.mem_union_right _ hep
  have hD₀ : disc₀ ⊆ U := Finset.subset_union_left
  have hfix : pass (pass^[U.card] disc₀) = pass^[U.card] disc₀ :=
    fixpoint_iterate_card pass U hinfl hbound disc₀ hD₀
  
  have hrun : runState (geomGuard endU endV) (geomStep endU endV) ω
      (repeatList l U.card) disc₀ = pass^[U.card] disc₀ :=
    runState_repeatList endU endV ω l U.card disc₀
  rw [hrun]
  exact saturated_of_fixpoint endU endV ω l (pass^[U.card] disc₀) hfix


omit [Fintype E] in


theorem mem_runState_repeatList_of_connOpenSet (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (hl : ∀ e, e ∈ l) (B : Set V) (disc₀ : Finset V)
    (hBdisc : ∀ b ∈ B, b ∈ disc₀) {o : V} (h : ConnOpenSet endU endV ω o B) :
    o ∈ runState (geomGuard endU endV) (geomStep endU endV) ω
        (repeatList l (disc₀ ∪ endpointsFinset endU endV l).card) disc₀ := by
  obtain ⟨b, hbB, hreach⟩ := h
  set N := (disc₀ ∪ endpointsFinset endU endV l).card with hN
  set D := runState (geomGuard endU endV) (geomStep endU endV) ω (repeatList l N) disc₀ with hD
  have hsat : Saturated endU endV ω l D := runState_repeatList_saturated endU endV ω l disc₀
  
  have hbD : b ∈ D := by
    have hbdisc : b ∈ disc₀ := hBdisc b hbB
    have hsub : disc₀ ⊆ D := by
      rw [hD, runState_repeatList]
      
      have : ∀ k, disc₀ ⊆ (fun D => runState (geomGuard endU endV) (geomStep endU endV) ω l D)^[k] disc₀ := by
        intro k; induction k with
        | zero => simp
        | succ j ih =>
            rw [Function.iterate_succ', Function.comp_apply]
            exact subset_trans ih (subset_runState endU endV ω l _)
      exact this N
    exact hsub hbdisc
  exact mem_of_reachOpen_of_saturated endU endV ω l D hsat hl hreach hbD


end TreeComplete
end OSSS
end StatMech
