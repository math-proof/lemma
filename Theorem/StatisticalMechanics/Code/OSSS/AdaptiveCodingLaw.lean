/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.GrandCouplingAssembly.Part6
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw
open scoped BigOperators
open MeasureTheory

set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace OSSS

namespace AdaptiveCodingLaw

open Coding GrandCoupling GrandCouplingAssembly Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma order_eq_on_prefix {n : ℕ} {σ : ConfigSpace E → (Fin n ≃ E)}
    (hσ : PredictableOrder σ) {x y : ConfigSpace E} {m : ℕ} (hm : m ≤ n)
    (hxy : Agree (prefixSet (σ x : Fin n → E) m) x y) :
    ∀ (i : ℕ) (hi : i < m),
      (σ y : Fin n → E) ⟨i, lt_of_lt_of_le hi hm⟩ =
        (σ x : Fin n → E) ⟨i, lt_of_lt_of_le hi hm⟩ := by
  intro i hi
  apply hσ x y
  intro e he
  apply hxy e
  obtain ⟨j, hj, rfl⟩ := (mem_prefixSet_iff (σ x : Fin n → E) i e).mp he
  rw [mem_prefixSet_iff]
  exact ⟨j, lt_trans hj hi, rfl⟩


lemma prefixSet_eq_of_predictable {n : ℕ} {σ : ConfigSpace E → (Fin n ≃ E)}
    (hσ : PredictableOrder σ) {x y : ConfigSpace E} {m : ℕ} (hm : m ≤ n)
    (hxy : Agree (prefixSet (σ x : Fin n → E) m) x y) :
    prefixSet (σ y : Fin n → E) m = prefixSet (σ x : Fin n → E) m := by
  ext e
  constructor
  · intro he
    obtain ⟨i, hi, hie⟩ := (mem_prefixSet_iff (σ y : Fin n → E) m e).mp he
    rw [mem_prefixSet_iff]
    refine ⟨i, hi, ?_⟩
    rw [← hie]
    exact (order_eq_on_prefix hσ hm hxy (i : ℕ) hi).symm
  · intro he
    obtain ⟨i, hi, hie⟩ := (mem_prefixSet_iff (σ x : Fin n → E) m e).mp he
    rw [mem_prefixSet_iff]
    refine ⟨i, hi, ?_⟩
    rw [← hie]
    exact order_eq_on_prefix hσ hm hxy (i : ℕ) hi


theorem codeMap_eq_unique_of_predictable (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (u : Fin n → ℝ) {x y : ConfigSpace E}
    (hx : codeMap μ (σ x : Fin n → E) u = x)
    (hy : codeMap μ (σ y : Fin n → E) u = y) :
    x = y := by
  have hbitsX := (codeMap_eq_iff μ (σ x) x u).mp hx
  have hbitsY := (codeMap_eq_iff μ (σ y) y u).mp hy
  have hagree : ∀ m : ℕ, m ≤ n →
      Agree (prefixSet (σ x : Fin n → E) m) x y := by
    intro m hm
    induction m with
    | zero =>
        intro e he
        simp [prefixSet, prefixIdx] at he
    | succ m ih =>
        have hmn : m < n := by omega
        have hmle : m ≤ n := Nat.le_of_lt hmn
        have hprev := ih hmle
        have hsel : (σ y : Fin n → E) ⟨m, hmn⟩ =
            (σ x : Fin n → E) ⟨m, hmn⟩ := hσ x y ⟨m, hmn⟩ hprev
        have hpref : prefixSet (σ y : Fin n → E) m =
            prefixSet (σ x : Fin n → E) m :=
          prefixSet_eq_of_predictable hσ hmle hprev
        have hthr : thr μ (σ y : Fin n → E) y ⟨m, hmn⟩ =
            thr μ (σ x : Fin n → E) x ⟨m, hmn⟩ := by
          unfold thr
          rw [hpref, hsel]
          apply condProbClosed_congr
          intro e he
          exact hprev e he
        have hnew : y ((σ x : Fin n → E) ⟨m, hmn⟩) =
            x ((σ x : Fin n → E) ⟨m, hmn⟩) := by
          have hxbit := hbitsX ⟨m, hmn⟩
          have hybit := hbitsY ⟨m, hmn⟩
          rw [hsel, hthr] at hybit
          exact hybit.trans hxbit.symm
        rw [prefixSet_succ_lt (σ x : Fin n → E) m hmn]
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hnew
        · exact hprev e he
  have hfull := hagree n le_rfl
  rw [prefixSet_card (σ x)] at hfull
  funext e
  exact (hfull e (Finset.mem_univ e)).symm


theorem predictable_fibres_disjoint (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    {x y : ConfigSpace E} (hxy : x ≠ y) :
    Disjoint {u | codeMap μ (σ x : Fin n → E) u = x}
      {u | codeMap μ (σ y : Fin n → E) u = y} := by
  rw [Set.disjoint_left]
  intro u hux huy
  exact hxy (codeMap_eq_unique_of_predictable μ σ hσ u hux huy)


end AdaptiveCodingLaw
end OSSS
end StatMech
