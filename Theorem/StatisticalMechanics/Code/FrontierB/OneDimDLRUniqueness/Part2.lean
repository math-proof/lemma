/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Def.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness.Part3
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

lemma wordHeadSplitEquiv_center (E : Type*) (m k n : ℕ) (s : E)
    (l : Fin m → E) (r : Fin (n + k + 1) → E) :
    wordHeadSplitEquiv E m k n (s, (l, r)) ⟨m, by omega⟩ = s := by
  exact splitPathEquiv_center E m (n + k + 1) s l r

lemma wordHeadSplitEquiv_right (E : Type*) (m k n : ℕ) (s : E)
    (l : Fin m → E) (r : Fin (n + k + 1) → E) (i : Fin (n + k + 1)) :
    wordHeadSplitEquiv E m k n (s, (l, r)) ⟨m + 1 + i.val, by omega⟩ = r i := by
  exact splitPathEquiv_right E m (n + k + 1) s l r i

lemma openMatrixProduct_wordHeadSplit {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a s b : E) (m k n : ℕ)
    (l : Fin m → E) (r : Fin (n + k + 1) → E) :
    openMatrixProduct A a b (wordHeadSplitEquiv E m k n (s, (l, r))) =
      openMatrixProduct A a s l * openMatrixProduct A s b r :=
  openMatrixProduct_split_factor A a s b m (n + k + 1) l r

lemma pathContainsWord_succ_split {E : Type*} (m k n : ℕ)
    (p : Fin (k + 2) → E) (s : E) (l : Fin m → E)
    (r : Fin (n + k + 1) → E) :
    pathContainsWord p (wordHeadSplitEquiv E m k n (s, (l, r))) ↔
      s = p 0 ∧ pathContainsWord (m := 0) (n := n) (Fin.tail p)
        ((pathCastEquiv E (by omega : 0 + (n + k) + 1 = n + k + 1)).symm r) := by
  constructor
  · intro hp
    constructor
    · have hi := hp 0
      rw [show (⟨m + (0 : Fin (k + 2)).val, by omega⟩ :
        Fin (m + (n + k + 1) + 1)) = ⟨m, by omega⟩ by apply Fin.ext; simp] at hi
      rw [wordHeadSplitEquiv_center] at hi
      exact hi
    · intro i
      have hi := hp (Fin.succ i)
      rw [show (⟨m + (Fin.succ i).val, by omega⟩ :
        Fin (m + (n + k + 1) + 1)) = ⟨m + 1 + i.val, by omega⟩ by
          apply Fin.ext
          change m + (i.val + 1) = m + 1 + i.val
          omega] at hi
      rw [wordHeadSplitEquiv_right E m k n s l r ⟨i.val, by omega⟩] at hi
      rw [pathCastEquiv_symm_apply E
        (by omega : 0 + (n + k) + 1 = n + k + 1) r]
      rw [show Fin.cast (by omega : 0 + (n + k) + 1 = n + k + 1)
        (⟨0 + i.val, by omega⟩ : Fin (0 + (n + k) + 1)) =
          ⟨i.val, by omega⟩ by apply Fin.ext; simp]
      exact hi
  · rintro ⟨hs, hp⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [show (⟨m + (0 : Fin (k + 2)).val, by omega⟩ :
        Fin (m + (n + k + 1) + 1)) = ⟨m, by omega⟩ by apply Fin.ext; simp]
      rw [wordHeadSplitEquiv_center, hs]
    · have hj := hp j
      rw [show (⟨m + (Fin.succ j).val, by omega⟩ :
        Fin (m + (n + k + 1) + 1)) = ⟨m + 1 + j.val, by omega⟩ by
          apply Fin.ext
          change m + (j.val + 1) = m + 1 + j.val
          omega]
      rw [wordHeadSplitEquiv_right E m k n s l r ⟨j.val, by omega⟩]
      rw [pathCastEquiv_symm_apply E
        (by omega : 0 + (n + k) + 1 = n + k + 1) r] at hj
      rw [show Fin.cast (by omega : 0 + (n + k) + 1 = n + k + 1)
        (⟨0 + j.val, by omega⟩ : Fin (0 + (n + k) + 1)) =
          ⟨j.val, by omega⟩ by apply Fin.ext; simp] at hj
      exact hj

lemma pathContainsWord_zero {E : Type*} (m n : ℕ) (p : Fin 1 → E)
    (q : Fin (m + (n + 0) + 1) → E) :
    pathContainsWord p q ↔ q ⟨m, by omega⟩ = p 0 := by
  constructor
  · intro hp
    exact hp 0
  · intro hp i
    fin_cases i
    exact hp

lemma fixedWordProduct_tail {E R : Type*} [CommMonoid R] (A : Matrix E E R)
    {k : ℕ} (p : Fin (k + 2) → E) :
    fixedWordProduct A p = A (p 0) (p 1) * fixedWordProduct A (Fin.tail p) := by
  unfold fixedWordProduct
  rw [Fin.prod_univ_succ]
  rfl

theorem sum_openMatrixProduct_fixedWord {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a b : E) :
    ∀ (k m n : ℕ) (p : Fin (k + 1) → E),
    (∑ q : Fin (m + (n + k) + 1) → E,
      if pathContainsWord p q then openMatrixProduct A a b q else 0) =
      (A ^ (m + 1)) a (p 0) * fixedWordProduct A p *
        (A ^ (n + 1)) (p (Fin.last k)) b := by
  classical
  intro k
  induction k generalizing a b with
  | zero =>
      intro m n p
      simp_rw [pathContainsWord_zero]
      simpa only [Nat.add_zero, fixedWordProduct, Fin.prod_univ_zero, mul_one,
        Fin.last_zero] using sum_openMatrixProduct_split A a (p 0) b m n
  | succ k ih =>
      intro m n p
      change (∑ q : Fin (m + (n + k + 1) + 1) → E,
        if pathContainsWord p q then openMatrixProduct A a b q else 0) = _
      rw [← Equiv.sum_comp (wordHeadSplitEquiv E m k n)
        (fun q => if pathContainsWord p q then openMatrixProduct A a b q else 0)]
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      simp_rw [pathContainsWord_succ_split, openMatrixProduct_wordHeadSplit]
      rw [Finset.sum_eq_single (p 0)]
      · simp only [true_and]
        have hif (l : Fin m → E) (r : Fin (n + k + 1) → E) :
            (if pathContainsWord (m := 0) (n := n) (Fin.tail p)
                ((pathCastEquiv E
                  (by omega : 0 + (n + k) + 1 = n + k + 1)).symm r) then
              openMatrixProduct A a (p 0) l * openMatrixProduct A (p 0) b r else 0) =
            openMatrixProduct A a (p 0) l *
              (if pathContainsWord (m := 0) (n := n) (Fin.tail p)
                  ((pathCastEquiv E
                    (by omega : 0 + (n + k) + 1 = n + k + 1)).symm r) then
                openMatrixProduct A (p 0) b r else 0) := by
          by_cases hpw : pathContainsWord (m := 0) (n := n) (Fin.tail p)
            ((pathCastEquiv E
              (by omega : 0 + (n + k) + 1 = n + k + 1)).symm r) <;> simp [hpw]
        simp_rw [hif]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul]
        rw [← matrix_pow_apply_eq_sum_open]
        let e : (Fin (0 + (n + k) + 1) → E) ≃ (Fin (n + k + 1) → E) :=
          pathCastEquiv E (by omega)
        have hsum : (∑ r : Fin (n + k + 1) → E,
              if pathContainsWord (m := 0) (n := n) (Fin.tail p) (e.symm r) then
                openMatrixProduct A (p 0) b r else 0) =
            ∑ q : Fin (0 + (n + k) + 1) → E,
              if pathContainsWord (m := 0) (n := n) (Fin.tail p) q then
                openMatrixProduct A (p 0) b q else 0 := by
          rw [← Equiv.sum_comp e]
          apply Finset.sum_congr rfl
          intro q hq
          simp only [Equiv.symm_apply_apply, e]
          rw [openMatrixProduct_pathCast]
        rw [hsum]
        rw [show (∑ q : Fin (0 + (n + k) + 1) → E,
            if pathContainsWord (m := 0) (n := n) (Fin.tail p) q then
              openMatrixProduct A (p 0) b q else 0) =
            (A ^ (0 + 1)) (p 0) ((Fin.tail p) 0) *
              fixedWordProduct A (Fin.tail p) *
                (A ^ (n + 1)) ((Fin.tail p) (Fin.last k)) b by
          exact ih (a := p 0) (b := b) 0 n (Fin.tail p)]
        rw [fixedWordProduct_tail]
        change (A ^ (m + 1)) a (p 0) *
            ((A ^ 1) (p 0) (p 1) * fixedWordProduct A (Fin.tail p) *
              (A ^ (n + 1)) (p (Fin.last (k + 1))) b) = _
        simp only [pow_one]
        ring
      · intro c hc hcp
        simp [hcp]
      · simp


end StatMech.FrontierB
