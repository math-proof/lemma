/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCycleComplete.Part2
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem walkOddSupport_nil (x : V) :
    walkOddSupport G (.nil : G.Walk x x) = ∅ := rfl

@[simp] theorem walkOddSupport_cons {u v w : V} (h : G.Adj u v)
    (p : G.Walk v w) :
    walkOddSupport G (.cons h p) = gaugeToggle s(u, v) (walkOddSupport G p) :=
  rfl

theorem walkOddSupport_subset_edgeFinset {x y : V} (p : G.Walk x y) :
    walkOddSupport G p ⊆ G.edgeFinset := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      intro e he
      rw [walkOddSupport_cons, mem_gaugeToggle] at he
      rcases he with ⟨rfl, _⟩ | ⟨_, he⟩
      · simpa using h
      · exact ih he


theorem filter_gaugeToggle_eq_of_not_mem
    {alpha : Type*} [DecidableEq alpha] (A S : Finset alpha) {a : alpha}
    (ha : a ∉ A) :
    A.filter (fun b => b ∈ gaugeToggle a S) = A.filter (fun b => b ∈ S) := by
  ext b
  by_cases hba : b = a
  · subst b
    simp [ha]
  · simp [mem_gaugeToggle, hba]


theorem filter_gaugeToggle_eq_toggle_of_mem
    {alpha : Type*} [DecidableEq alpha] (A S : Finset alpha) {a : alpha}
    (ha : a ∈ A) :
    A.filter (fun b => b ∈ gaugeToggle a S) =
      gaugeToggle a (A.filter (fun b => b ∈ S)) := by
  ext b
  by_cases hba : b = a
  · subst b
    simp [ha, mem_gaugeToggle]
  · simp [mem_gaugeToggle, hba]


theorem even_card_gaugeToggle_iff_not_even
    {alpha : Type*} [DecidableEq alpha] (a : alpha) (S : Finset alpha) :
    Even (gaugeToggle a S).card ↔ ¬ Even S.card := by
  by_cases ha : a ∈ S
  · rw [gaugeToggle, if_pos ha, card_erase_of_mem ha]
    rw [Nat.even_sub (by exact card_pos.mpr ⟨a, ha⟩)]
    simp
  · rw [gaugeToggle, if_neg ha, card_insert_of_notMem ha,
      Nat.even_add_one]


theorem even_filter_walkOddSupport_iff_walkParity_false
    (A : Finset (Sym2 V)) {x y : V} (p : G.Walk x y) :
    Even (A.filter (fun e => e ∈ walkOddSupport G p)).card ↔
      walkParity G A p = false := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      by_cases he : s(u, v) ∈ A
      · rw [walkOddSupport_cons,
          filter_gaugeToggle_eq_toggle_of_mem A (walkOddSupport G p) he,
          even_card_gaugeToggle_iff_not_even, walkParity_cons]
        rw [ih]
        cases walkParity G A p <;> simp [he]
      · rw [walkOddSupport_cons,
          filter_gaugeToggle_eq_of_not_mem A (walkOddSupport G p) he,
          walkParity_cons, ih]
        simp [he]


end
end StatMech.FrontierA
