/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFourFunctions
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]

theorem lpReplicaToggleRows_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    Function.Involutive (lpReplicaToggleRows G sites m P) := by
  intro tag
  funext c
  by_cases hc : c ∈ P
  · cases htag : tag c with
    | mk row current =>
      cases row <;> cases current <;>
        simp [lpReplicaToggleRows, hc, htag]
  · simp [lpReplicaToggleRows, hc]

theorem lpReplicaRowCopies_toggle
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    lpReplicaRowCopies G sites m (lpReplicaToggleRows G sites m P tag) row =
      lpReplicaRowCopies G sites m tag row ∆ P := by
  ext c
  by_cases hc : c ∈ P <;> cases hrow : (tag c).1 <;> cases row <;>
    simp [lpReplicaRowCopies, lpReplicaToggleRows, hc, hrow,
      Finset.mem_symmDiff]

theorem lpReplicaCurrentCopies_toggle
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    lpReplicaCurrentCopies G sites m
        (lpReplicaToggleRows G sites m P tag) row current =
      lpReplicaCurrentCopies G sites m tag row current ∆
        P.filter (fun c => (tag c).2 = current) := by
  ext c
  simp only [lpReplicaCurrentCopies, lpReplicaToggleRows, mem_filter,
    mem_univ, true_and, Finset.mem_symmDiff]
  by_cases hc : c ∈ P
  · simp only [hc, if_pos, true_and]
    rcases htag : tag c with ⟨r, q⟩
    cases r <;> cases q <;> cases row <;> cases current <;> simp
  · simp only [hc, if_neg, false_and, not_false_eq_true, and_true,
      or_false]

omit [DecidableEq V] in
theorem lpReplicaCurrentCopies_subset_rowCopies
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    lpReplicaCurrentCopies G sites m tag row current ⊆
      lpReplicaRowCopies G sites m tag row := by
  intro c hc
  simp only [lpReplicaCurrentCopies, lpReplicaRowCopies, mem_filter,
    mem_univ, true_and] at hc ⊢
  exact congrArg Prod.fst hc

theorem lpReplicaRowCopies_eq_current_symmDiff
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    lpReplicaRowCopies G sites m tag row =
      lpReplicaCurrentCopies G sites m tag row false ∆
        lpReplicaCurrentCopies G sites m tag row true := by
  ext c
  cases htag : tag c with
  | mk r q =>
    cases r <;> cases q <;> cases row <;>
      simp [lpReplicaRowCopies, lpReplicaCurrentCopies, htag,
        Finset.mem_symmDiff]

theorem lpReplicaRowSources_toggle
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P tag) row) =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (lpReplicaRowCopies G sites m tag row) ∆
        RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) P := by
  rw [lpReplicaRowCopies_toggle, RandomCurrent.sources_symmDiff]

theorem lpReplicaCurrentSources_toggle
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaCurrentCopies G sites m
          (lpReplicaToggleRows G sites m P tag) row current) =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (lpReplicaCurrentCopies G sites m tag row current) ∆
        RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (P.filter (fun c => (tag c).2 = current)) := by
  rw [lpReplicaCurrentCopies_toggle, RandomCurrent.sources_symmDiff]

theorem lpReplicaRowSources_eq_currentSources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m tag row) =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (lpReplicaCurrentCopies G sites m tag row false) ∆
        RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (lpReplicaCurrentCopies G sites m tag row true) := by
  rw [lpReplicaRowCopies_eq_current_symmDiff,
    RandomCurrent.sources_symmDiff]

end
end StatMech.Ising
