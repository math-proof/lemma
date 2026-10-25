/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.FrontierA.GrahamThreeGateBoundaryCounterexample
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent


theorem not_connK_of_closed_vertex_set
    {I W : Type*} [DecidableEq I] [DecidableEq W]
    {ends : I -> Sym2 W} {E : Finset I} {C : Finset W} {u v : W}
    (hu : u ∈ C) (hv : v ∉ C)
    (hclosed : ∀ i ∈ E, ∀ a ∈ ends i, a ∈ C ->
      ∀ b ∈ ends i, b ∈ C) :
    ¬ connK ends E u v := by
  intro huv
  apply hv
  have hmem : ∀ x, connK ends E u x -> x ∈ C := by
    intro x hux
    induction hux with
    | refl => exact hu
    | tail hab hstep ih =>
        rcases hstep with ⟨i, hi, ha, hb, -⟩
        exact hclosed i hi _ ha ih _ hb
  exact hmem v huv

theorem threeGateCounter_closed
    (E : Finset (Fin 15)) (C : Finset (Fin 6))
    (hEC : (E = threeGateCounterK ∧ C = {0, 1}) ∨
      (E = threeGateCounterS ∧ C = {0, 1, 5}) ∨
      (E = threeGateCounterN ∧ C = {1})) :
    ∀ i ∈ E, ∀ a ∈ threeGateCounterEnds i, a ∈ C ->
      ∀ b ∈ threeGateCounterEnds i, b ∈ C := by
  rcases hEC with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    intro i hi a ha haC b hb <;>
    fin_cases i <;>
    simp [threeGateCounterK, threeGateCounterS, threeGateCounterN,
      threeGateCounterEnds] at hi ha haC hb ⊢ <;> aesop

theorem threeGateCounter_complement_closed
    (E : Finset (Fin 15))
    (hE : E = threeGateCounterK ∨
      E = threeGateCounterS ∨ E = threeGateCounterN) :
    ∀ i ∈ threeGateCounterSupport \ E,
      ∀ a ∈ threeGateCounterEnds i, a ∈ ({0, 1, 2, 4, 5} : Finset (Fin 6)) ->
      ∀ b ∈ threeGateCounterEnds i, b ∈ ({0, 1, 2, 4, 5} : Finset (Fin 6)) := by
  rcases hE with rfl | rfl | rfl <;>
    intro i hi a ha haC b hb <;>
    fin_cases i <;>
    simp [threeGateCounterSupport, threeGateCounterK,
      threeGateCounterS, threeGateCounterN,
      threeGateCounterEnds] at hi ha haC hb ⊢ <;> aesop

theorem threeGateCounter_boundaries :
    sources threeGateCounterEnds threeGateCounterSupport = {0, 2} /\
      sources threeGateCounterEnds threeGateCounterK = {0, 1} /\
      sources threeGateCounterEnds threeGateCounterS = {0, 1} /\
      sources threeGateCounterEnds threeGateCounterN = {0, 2} /\
      sources threeGateCounterEnds threeGateCounterA = {0, 2} := by
  decide

theorem threeGateCounter_threefold :
    threeGateCounterK ∆ threeGateCounterS ∆ threeGateCounterN =
      threeGateCounterA := by
  decide

theorem threeGateCounter_complement_not_conn
    (E : Finset (Fin 15))
    (hE : E = threeGateCounterK ∨
      E = threeGateCounterS ∨ E = threeGateCounterN) :
    ¬ connK threeGateCounterEnds (threeGateCounterSupport \ E) 1 3 := by
  apply not_connK_of_closed_vertex_set
    (C := ({0, 1, 2, 4, 5} : Finset (Fin 6)))
  · simp
  · simp
  · exact threeGateCounter_complement_closed E hE

theorem threeGateCounter_K_gated :
    ThreeGateCounterGated threeGateCounterK := by
  constructor
  · apply not_connK_of_closed_vertex_set
      (C := ({0, 1} : Finset (Fin 6))) (by simp) (by simp)
    exact threeGateCounter_closed _ _ (Or.inl ⟨rfl, rfl⟩)
  · exact threeGateCounter_complement_not_conn _ (Or.inl rfl)

theorem threeGateCounter_S_gated :
    ThreeGateCounterGated threeGateCounterS := by
  constructor
  · apply not_connK_of_closed_vertex_set
      (C := ({0, 1, 5} : Finset (Fin 6))) (by simp) (by simp)
    exact threeGateCounter_closed _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact threeGateCounter_complement_not_conn _ (Or.inr (Or.inl rfl))

theorem threeGateCounter_N_gated :
    ThreeGateCounterGated threeGateCounterN := by
  constructor
  · apply not_connK_of_closed_vertex_set
      (C := ({1} : Finset (Fin 6))) (by simp) (by simp)
    exact threeGateCounter_closed _ _ (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · exact threeGateCounter_complement_not_conn _ (Or.inr (Or.inr rfl))

theorem threeGateCounter_A_conn :
    connK threeGateCounterEnds threeGateCounterA 1 3 := by
  have h15 : connK threeGateCounterEnds threeGateCounterA 1 5 :=
    Relation.ReflTransGen.single ⟨8, by simp [threeGateCounterA],
      by simp [threeGateCounterEnds], by simp [threeGateCounterEnds], by decide⟩
  have h50 : adjStep threeGateCounterEnds threeGateCounterA 5 0 :=
    ⟨4, by simp [threeGateCounterA], by simp [threeGateCounterEnds],
      by simp [threeGateCounterEnds], by decide⟩
  have h02 : adjStep threeGateCounterEnds threeGateCounterA 0 2 :=
    ⟨1, by simp [threeGateCounterA], by simp [threeGateCounterEnds],
      by simp [threeGateCounterEnds], by decide⟩
  have h23 : adjStep threeGateCounterEnds threeGateCounterA 2 3 :=
    ⟨9, by simp [threeGateCounterA], by simp [threeGateCounterEnds],
      by simp [threeGateCounterEnds], by decide⟩
  exact ((h15.tail h50).tail h02).tail h23


theorem threeGate_boundaryOnly_closure_false :
    sources threeGateCounterEnds threeGateCounterSupport = {0, 2} ∧
      sources threeGateCounterEnds threeGateCounterK = {0, 1} ∧
      sources threeGateCounterEnds threeGateCounterS = {0, 1} ∧
      sources threeGateCounterEnds threeGateCounterN = {0, 2} ∧
      threeGateCounterK ∆ threeGateCounterS ∆ threeGateCounterN =
        threeGateCounterA ∧
      ThreeGateCounterGated threeGateCounterK ∧
      ThreeGateCounterGated threeGateCounterS ∧
      ThreeGateCounterGated threeGateCounterN ∧
      ¬ ThreeGateCounterGated threeGateCounterA := by
  refine ⟨threeGateCounter_boundaries.1,
    threeGateCounter_boundaries.2.1,
    threeGateCounter_boundaries.2.2.1,
    threeGateCounter_boundaries.2.2.2.1,
    threeGateCounter_threefold,
    threeGateCounter_K_gated,
    threeGateCounter_S_gated,
    threeGateCounter_N_gated, ?_⟩
  intro hA
  exact hA.1 threeGateCounter_A_conn


end StatMech.GrahamGHS.FourColor
