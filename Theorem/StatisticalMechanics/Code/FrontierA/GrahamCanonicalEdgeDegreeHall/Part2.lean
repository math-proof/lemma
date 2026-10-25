/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightRootCutHallEquivalence
import Instance.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall
open Finset
open scoped symmDiff


namespace StatMech.FrontierA

variable {A B : Type*} [Fintype A] [Fintype B]


theorem bipartiteLeftSurplusToken_eq_of_source_target_eq
    [DecidableEq B] (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A) (base : ↑S -> B)
    {x y : bipartiteLeftSurplusToken r S base}
    (hsource : x.1 = y.1) (htarget : x.2.1 = y.2.1) : x = y := by
  rcases x with ⟨xsource, xtarget, hx⟩
  rcases y with ⟨ysource, ytarget, hy⟩
  simp only at hsource htarget
  subst ysource
  subst ytarget
  rfl


theorem cycleCollisionAndSurplusTokenEmbeddings
    {C : Type*} [Fintype C]
    [DecidableEq A] [DecidableEq B]
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A) (N : Finset B)
    (leftBase : ↑S -> B) (rightBase : ↑N -> A)
    (σ : Equiv.Perm C) (source : C -> ↑S) (target : C -> ↑N)
    (hσ : ∀ x, σ x ≠ x)
    (htarget : Function.Injective target)
    (hsourceNext : ∀ x, source x ≠ source (σ x))
    (hcurrent : ∀ x, r (source x).1 (target x).1)
    (hnext : ∀ x, r (source x).1 (target (σ x)).1)
    (hexceptional : ∀ x, (source x).1 ≠ rightBase (target x)) :
    Nonempty (C ↪ bipartiteRightCollisionToken r S N rightBase) ∧
      Nonempty (C ↪ bipartiteLeftSurplusToken r S leftBase) := by
  classical
  have hrightMem (x : C) : (source x).1 ∈
      (S.filter fun a => r a (target x).1).erase (rightBase (target x)) := by
    apply Finset.mem_erase.mpr
    exact ⟨hexceptional x,
      Finset.mem_filter.mpr ⟨(source x).2, hcurrent x⟩⟩
  let rightToken : C -> bipartiteRightCollisionToken r S N rightBase :=
    fun x => ⟨target x, ⟨(source x).1, hrightMem x⟩⟩
  have hrightInjective : Function.Injective rightToken := by
    intro x y hxy
    apply htarget
    exact congrArg Sigma.fst hxy
  let outputTarget : C -> B := fun x =>
    if (target x).1 = leftBase (source x) then
      (target (σ x)).1 else (target x).1
  have houtputRelated (x : C) : r (source x).1 (outputTarget x) := by
    dsimp only [outputTarget]
    split
    · exact hnext x
    · exact hcurrent x
  have houtputNe (x : C) : outputTarget x ≠ leftBase (source x) := by
    dsimp only [outputTarget]
    split
    next heq =>
      intro hnextBase
      apply hσ x
      apply htarget
      apply Subtype.ext
      exact hnextBase.trans heq.symm
    next hne => exact hne
  have hleftMem (x : C) : outputTarget x ∈
      (Finset.univ.filter (r (source x).1)).erase (leftBase (source x)) := by
    apply Finset.mem_erase.mpr
    exact ⟨houtputNe x,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, houtputRelated x⟩⟩
  let leftToken : C -> bipartiteLeftSurplusToken r S leftBase :=
    fun x => ⟨source x, ⟨outputTarget x, hleftMem x⟩⟩
  have hleftInjective : Function.Injective leftToken := by
    intro x y hxy
    have hsourceEq : source x = source y := congrArg Sigma.fst hxy
    have htargetEq : outputTarget x = outputTarget y := by
      exact congrArg (fun z => z.2.1) hxy
    by_cases hx : (target x).1 = leftBase (source x)
    · by_cases hy : (target y).1 = leftBase (source y)
      · apply σ.injective
        apply htarget
        apply Subtype.ext
        simpa only [outputTarget, if_pos hx, if_pos hy] using htargetEq
      · have hindex : σ x = y := by
          apply htarget
          apply Subtype.ext
          simpa only [outputTarget, if_pos hx, if_neg hy] using htargetEq
        exfalso
        apply hsourceNext x
        rw [hindex]
        exact hsourceEq
    · by_cases hy : (target y).1 = leftBase (source y)
      · have hindex : x = σ y := by
          apply htarget
          apply Subtype.ext
          simpa only [outputTarget, if_neg hx, if_pos hy] using htargetEq
        exfalso
        apply hsourceNext y
        rw [← hindex]
        exact hsourceEq.symm
      · apply htarget
        apply Subtype.ext
        simpa only [outputTarget, if_neg hx, if_neg hy] using htargetEq
  exact ⟨⟨⟨rightToken, hrightInjective⟩⟩,
    ⟨⟨leftToken, hleftInjective⟩⟩⟩


end StatMech.FrontierA
