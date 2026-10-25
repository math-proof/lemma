/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part3


namespace StatMech.FrontierA

noncomputable def embeddingSumOfCrossCollisionCharge
    {A B C : Type*} (f : A ↪ C) (g : B ↪ C)
    (charge : crossCollision f g ↪ C)
    (hfreshLeft : ∀ collision a, charge collision ≠ f a)
    (hfreshRight : ∀ collision b, charge collision ≠ g b) :
    A ⊕ B ↪ C := by
  classical
  let hasCollision := fun b : B => ∃ a : A, f a = g b
  let chosenCollision (b : B) (h : hasCollision b) : crossCollision f g :=
    ⟨(Classical.choose h, b), Classical.choose_spec h⟩
  let merged : A ⊕ B -> C
    | Sum.inl a => f a
    | Sum.inr b => if h : hasCollision b then charge (chosenCollision b h)
        else g b
  refine ⟨merged, ?_⟩
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl a' =>
          simp only [merged, f.injective.eq_iff] at hxy
          exact congrArg Sum.inl hxy
      | inr b =>
          by_cases hb : hasCollision b
          · simp only [merged, dif_pos hb] at hxy
            exact False.elim (hfreshLeft (chosenCollision b hb) a hxy.symm)
          · simp only [merged, dif_neg hb] at hxy
            exact False.elim (hb ⟨a, hxy⟩)
  | inr b =>
      cases y with
      | inl a =>
          by_cases hb : hasCollision b
          · simp only [merged, dif_pos hb] at hxy
            exact False.elim (hfreshLeft (chosenCollision b hb) a hxy)
          · simp only [merged, dif_neg hb] at hxy
            exact False.elim (hb ⟨a, hxy.symm⟩)
      | inr b' =>
          by_cases hb : hasCollision b
          · by_cases hb' : hasCollision b'
            · simp only [merged, dif_pos hb, dif_pos hb'] at hxy
              have hcollision := charge.injective hxy
              have hpair := congrArg Subtype.val hcollision
              exact congrArg Sum.inr (congrArg Prod.snd hpair)
            · simp only [merged, dif_pos hb, dif_neg hb'] at hxy
              exact False.elim
                (hfreshRight (chosenCollision b hb) b' hxy)
          · by_cases hb' : hasCollision b'
            · simp only [merged, dif_neg hb, dif_pos hb'] at hxy
              exact False.elim
                (hfreshRight (chosenCollision b' hb') b hxy.symm)
            · simp only [merged, dif_neg hb, dif_neg hb'] at hxy
              exact congrArg Sum.inr (g.injective hxy)


noncomputable def embeddingSumOfCrossCollisionSecondCharge
    {A B C : Type*} (f : A ↪ C) (g : B ↪ C)
    (first : crossCollision f g ↪ C)
    (hfirstFreshLeft : ∀ collision a, first collision ≠ f a)
    (second : crossCollision first g ↪ C)
    (hsecondFreshLeft : ∀ collision a, second collision ≠ f a)
    (hsecondFreshRight : ∀ collision b, second collision ≠ g b)
    (hsecondFreshFirst : ∀ collision old, second collision ≠ first old) :
    A ⊕ B ↪ C := by
  classical
  let hasFirst := fun b : B => ∃ a : A, f a = g b
  let chosenFirst (b : B) (h : hasFirst b) : crossCollision f g :=
    ⟨(Classical.choose h, b), Classical.choose_spec h⟩
  let hasSecond := fun b : B => ∃ old : crossCollision f g, first old = g b
  let chosenSecond (b : B) (h : hasSecond b) : crossCollision first g :=
    ⟨(Classical.choose h, b), Classical.choose_spec h⟩
  let merged : A ⊕ B -> C
    | Sum.inl a => f a
    | Sum.inr b => if h₁ : hasFirst b then first (chosenFirst b h₁)
        else if h₂ : hasSecond b then second (chosenSecond b h₂) else g b
  refine ⟨merged, ?_⟩
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl a' =>
          simp only [merged, f.injective.eq_iff] at hxy
          exact congrArg Sum.inl hxy
      | inr b =>
          by_cases h₁ : hasFirst b
          · simp only [merged, dif_pos h₁] at hxy
            exact False.elim
              (hfirstFreshLeft (chosenFirst b h₁) a hxy.symm)
          · by_cases h₂ : hasSecond b
            · simp only [merged, dif_neg h₁, dif_pos h₂] at hxy
              exact False.elim
                (hsecondFreshLeft (chosenSecond b h₂) a hxy.symm)
            · simp only [merged, dif_neg h₁, dif_neg h₂] at hxy
              exact False.elim (h₁ ⟨a, hxy⟩)
  | inr b =>
      cases y with
      | inl a =>
          by_cases h₁ : hasFirst b
          · simp only [merged, dif_pos h₁] at hxy
            exact False.elim (hfirstFreshLeft (chosenFirst b h₁) a hxy)
          · by_cases h₂ : hasSecond b
            · simp only [merged, dif_neg h₁, dif_pos h₂] at hxy
              exact False.elim
                (hsecondFreshLeft (chosenSecond b h₂) a hxy)
            · simp only [merged, dif_neg h₁, dif_neg h₂] at hxy
              exact False.elim (h₁ ⟨a, hxy.symm⟩)
      | inr b' =>
          by_cases h₁ : hasFirst b
          · by_cases h₁' : hasFirst b'
            · simp only [merged, dif_pos h₁, dif_pos h₁'] at hxy
              have hc := first.injective hxy
              exact congrArg Sum.inr (congrArg (fun z => z.1.2) hc)
            · by_cases h₂' : hasSecond b'
              · simp only [merged, dif_pos h₁, dif_neg h₁',
                  dif_pos h₂'] at hxy
                exact False.elim
                  (hsecondFreshFirst (chosenSecond b' h₂')
                    (chosenFirst b h₁) hxy.symm)
              · simp only [merged, dif_pos h₁, dif_neg h₁',
                  dif_neg h₂'] at hxy
                exact False.elim (h₂' ⟨chosenFirst b h₁, hxy⟩)
          · by_cases h₁' : hasFirst b'
            · by_cases h₂ : hasSecond b
              · simp only [merged, dif_neg h₁, dif_pos h₂,
                  dif_pos h₁'] at hxy
                exact False.elim
                  (hsecondFreshFirst (chosenSecond b h₂)
                    (chosenFirst b' h₁') hxy)
              · simp only [merged, dif_neg h₁, dif_neg h₂,
                  dif_pos h₁'] at hxy
                exact False.elim (h₂ ⟨chosenFirst b' h₁', hxy.symm⟩)
            · by_cases h₂ : hasSecond b
              · by_cases h₂' : hasSecond b'
                · simp only [merged, dif_neg h₁, dif_pos h₂,
                    dif_neg h₁', dif_pos h₂'] at hxy
                  have hc := second.injective hxy
                  exact congrArg Sum.inr (congrArg (fun z => z.1.2) hc)
                · simp only [merged, dif_neg h₁, dif_pos h₂,
                    dif_neg h₁', dif_neg h₂'] at hxy
                  exact False.elim
                    (hsecondFreshRight (chosenSecond b h₂) b' hxy)
              · by_cases h₂' : hasSecond b'
                · simp only [merged, dif_neg h₁, dif_neg h₂,
                    dif_neg h₁', dif_pos h₂'] at hxy
                  exact False.elim
                    (hsecondFreshRight (chosenSecond b' h₂') b hxy.symm)
                · simp only [merged, dif_neg h₁, dif_neg h₂,
                    dif_neg h₁', dif_neg h₂'] at hxy
                  exact congrArg Sum.inr (g.injective hxy)


end StatMech.FrontierA
