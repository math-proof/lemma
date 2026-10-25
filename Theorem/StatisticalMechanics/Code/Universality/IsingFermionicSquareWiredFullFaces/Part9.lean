/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

theorem fkIsingSquareWiredFullCycle_injective
    (n : Nat) (hn : 0 < n) :
    Function.Injective (fkIsingSquareWiredFullCycle n hn) := by
  intro a b hab
  rcases a with c | o <;> rcases b with d | p
  · exact congrArg Sum.inl
      (fkIsingSquareWiredFullInteriorCycle_injective n hn hab)
  · cases p with
    | none => exact (fkIsingSquareWiredFullInteriorCycle_ne_exterior
        n hn c hab).elim
    | some k => exact (fkIsingSquareWiredFullInteriorCycle_ne_left
        n hn c k hab).elim
  · cases o with
    | none => exact (fkIsingSquareWiredFullInteriorCycle_ne_exterior
        n hn d hab.symm).elim
    | some k => exact (fkIsingSquareWiredFullInteriorCycle_ne_left
        n hn d k hab.symm).elim
  · cases o with
    | none =>
        cases p with
        | none => rfl
        | some k => exact (fkIsingSquareWiredFullLeftCycle_ne_exterior
            n hn k hab.symm).elim
    | some k =>
        cases p with
        | none => exact (fkIsingSquareWiredFullLeftCycle_ne_exterior
            n hn k hab).elim
        | some l =>
            exact congrArg (fun j => Sum.inr (some j))
              (fkIsingSquareWiredFullLeftCycle_injective n hn hab)

theorem fkIsingSquareWired_full_completed_componentCount_lower
    (n : Nat) (hn : 0 < n) :
    (2 * n + 1) ^ 2 - 2 * n ≤
      Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent := by
  have hcard := Nat.card_le_card_of_injective
    (fkIsingSquareWiredFullCycle n hn)
    (fkIsingSquareWiredFullCycle_injective n hn)
  rw [StatMech.FrontierA.natCard_permCycleClass,
    permCycleCount_fkIsingSquareWiredBlackBoundaryPerm] at hcard
  have hsource : Nat.card (FKIsingSquareWiredFullCycleIndex n) =
      (2 * n + 1) ^ 2 - 2 * n := by
    rw [Nat.card_eq_fintype_card]
    simp [FKIsingSquareWiredFullCycleIndex, FKIsingSquareInteriorCell]
    have hid : (2 * n + 1) ^ 2 =
        (2 * n) * (2 * n) + (2 * n + 1) + 2 * n := by ring
    omega
  rwa [hsource] at hcard

theorem fkIsingSquareWiredEulerDefect_empty_le_full
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅) ≤
      fkIsingSquareWiredEulerDefect n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) := by
  classical
  let E := (fkSquareBoxPlanar n).G.edgeFinset
  let defect := fkIsingSquareWiredEulerDefect n hn
  let F : Finset (Sym2 (fkSquareBoxPlanar n).V) → Int :=
    fun A ↦ defect (FK.edgeSetConfig (A ∩ E))
  have hinsert : ∀ (A : Finset (Sym2 (fkSquareBoxPlanar n).V))
      (e : Sym2 (fkSquareBoxPlanar n).V), e ∉ A → F A ≤ F (insert e A) := by
    intro A e heA
    by_cases heE : e ∈ E
    · let em : FKIsingMedialVertex (fkSquareBoxPlanar n) :=
        ⟨e, by simpa only [E, SimpleGraph.mem_edgeFinset] using heE⟩
      have heAE : e ∉ A ∩ E := by simp [heA]
      have hclosed : setClosed e (FK.edgeSetConfig (A ∩ E)) =
          FK.edgeSetConfig (A ∩ E) := by
        funext f
        by_cases hfe : f = e
        · subst f
          simp [FK.edgeSetConfig, heAE]
        · simp [setClosed, hfe]
      have hopen : setOpen e (FK.edgeSetConfig (A ∩ E)) =
          FK.edgeSetConfig (insert e A ∩ E) := by
        funext f
        by_cases hfe : f = e
        · subst f
          simp [FK.edgeSetConfig, heE]
        · simp [FK.edgeSetConfig, setOpen, hfe]
      have hmono := fkIsingSquareWiredEulerDefect_setClosed_le_setOpen
        n hn (FK.edgeSetConfig (A ∩ E)) em
      simpa only [F, defect, em, hclosed, hopen] using hmono
    · have hinter : insert e A ∩ E = A ∩ E := by
        ext f
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hfA, hfE⟩
          · exact False.elim (heE hfE)
          · exact ⟨hfA, hfE⟩
        · rintro ⟨hfA, hfE⟩
          exact ⟨Or.inr hfA, hfE⟩
      rw [show F (insert e A) = F A by simp only [F, hinter]]
  have hmono : Monotone F :=
    Finset.monotone_iff_forall_le_insert.mpr hinsert
  have h := hmono (Finset.empty_subset E)
  simpa [F, defect, E] using h


theorem fkIsingSquareWired_full_completed_componentCount
    (n : Nat) (hn : 0 < n) :
    Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
        (FK.edgeSetConfig
          (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent =
      (2 * n + 1) ^ 2 - 2 * n := by
  apply le_antisymm
  · have hdef := fkIsingSquareWiredEulerDefect_empty_le_full n hn
    rw [fkIsingSquareWiredEulerDefect_empty_formula,
      fkIsingSquareWiredEulerDefect_full_formula,
      fkIsingSquareWired_empty_completed_componentCount n hn] at hdef
    have hcast :
        (Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
          (FK.edgeSetConfig
            (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent : Int) ≤
          ((2 * n + 1) ^ 2 - 2 * n : Nat) := by
      omega
    exact_mod_cast hcast
  · exact fkIsingSquareWired_full_completed_componentCount_lower n hn


theorem fkIsingSquareWiredEulerDefect_empty_full
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredEulerDefect n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) =
      fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅) := by
  apply (fkIsingSquareWiredEulerDefect_empty_full_iff_componentCount n hn).2
  rw [fkIsingSquareWired_full_completed_componentCount n hn,
    fkIsingSquareWired_empty_completed_componentCount n hn]


theorem fkIsingSquareWiredEulerDefect_toggle_eq
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredEulerDefect n hn (setOpen e.1 omega) =
      fkIsingSquareWiredEulerDefect n hn (setClosed e.1 omega) :=
  fkIsingSquareWiredEulerDefect_toggle_eq_of_empty_full_eq n hn
    (fkIsingSquareWiredEulerDefect_empty_full n hn) omega e

end
end StatMech.Universality
