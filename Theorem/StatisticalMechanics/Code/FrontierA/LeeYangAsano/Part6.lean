/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.LeeYangPolynomial
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Theorem.StatisticalMechanics.Code.FrontierC.LeeYangSymmetry.Part2
import Def.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part5
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem leeYangMonomial_update {I : Type*} [DecidableEq I]
    (S : Finset I) (z : I → ℂ) (i : I) (u : ℂ) :
    leeYangMonomial S (Function.update z i u) =
      if i ∈ S then u * leeYangMonomial (S.erase i) z else leeYangMonomial S z := by
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    unfold leeYangMonomial
    rw [← Finset.mul_prod_erase S (fun k ↦ Function.update z i u k) hi]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro k hk
      have hki : k ≠ i := (Finset.mem_erase.mp hk).1
      simp [hki]
  · rw [if_neg hi]
    unfold leeYangMonomial
    apply Finset.prod_congr rfl
    intro k hk
    have hki : k ≠ i := fun h ↦ hi (h ▸ hk)
    simp [hki]

theorem asanoContract_add {I : Type*} [DecidableEq I]
    (p q : (I → ℂ) → ℂ) (i j : I) :
    asanoContract (fun z ↦ p z + q z) i j =
      fun z ↦ asanoContract p i j z + asanoContract q i j z := by
  funext z
  simp only [asanoContract]
  ring

theorem asanoContract_sum {I A : Type*} [DecidableEq I] [DecidableEq A]
    (s : Finset A) (p : A → (I → ℂ) → ℂ) (i j : I) :
    asanoContract (fun z ↦ ∑ a ∈ s, p a z) i j =
      fun z ↦ ∑ a ∈ s, asanoContract (p a) i j z := by
  induction s using Finset.induction with
  | empty =>
      funext z
      simp [asanoContract]
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [asanoContract_add, ih]

theorem asanoContract_monomial {I : Type*} [DecidableEq I]
    (S : Finset I) (z : I → ℂ) {i j : I} (hij : i ≠ j) :
    asanoContract (leeYangMonomial S) i j z =
      if (i ∈ S ↔ j ∈ S) then
        leeYangMonomial (S.erase j) z else 0 := by
  unfold asanoContract
  simp_rw [leeYangMonomial_update]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp_all [Finset.mem_erase]
    unfold leeYangMonomial
    exact Finset.mul_prod_erase (S.erase j) z (Finset.mem_erase.mpr ⟨hij, hi⟩)
  · simp_all
  · simp_all [Finset.mem_erase]
  · simp_all

end StatMech.FrontierA
