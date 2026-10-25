/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Instance.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part2
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

@[simp] theorem shbK4Edge_code_mem_image_iff
    (A : Finset shbK4Edge) (k : shbK4Edge) :
    k.code ∈ A.image shbK4Edge.code ↔ k ∈ A := by
  constructor
  · intro h
    obtain ⟨k', hk', hcode⟩ := Finset.mem_image.mp h
    simpa [shbK4Edge.code_injective hcode] using hk'
  · exact fun hk ↦ Finset.mem_image.mpr ⟨k, hk, rfl⟩

@[simp] theorem shbK4Edge_forall_eq_code_mem_image_iff
    (A : Finset shbK4Edge) (k : shbK4Edge) :
    (∀ e : Sym2 (Fin 4), e = k.code →
      e ∈ A.image shbK4Edge.code) ↔ k ∈ A := by
  constructor
  · intro h
    exact (shbK4Edge_code_mem_image_iff A k).mp (h k.code rfl)
  · intro hk e he
    subst e
    exact (shbK4Edge_code_mem_image_iff A k).mpr hk

theorem shbK4_support_lt_direct_classification (l : List (Fin 4))
    (hnodup : l.Nodup) (hfirst : l.head? = some 0)
    (hlast : l.getLast? = some 3) (hlt : l < [(0 : Fin 4), 3]) :
    l = [0, 1, 2, 3] ∨ l = [0, 1, 3] ∨
      l = [0, 2, 1, 3] ∨ l = [0, 2, 3] := by
  rcases l with _ | ⟨a, l⟩
  · simp at hfirst
  simp only [List.head?_cons, Option.some.injEq] at hfirst
  subst a
  rcases l with _ | ⟨b, l⟩
  · simp at hlast
  have hlen : l.length ≤ 2 := by
    have hcard := hnodup.length_le_card
    simp at hcard
    omega
  rcases l with _ | ⟨c, l⟩
  · fin_cases b <;> simp_all
  rcases l with _ | ⟨d, l⟩
  · fin_cases b <;> fin_cases c <;> simp_all
  have : l = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp_all
  subst l
  fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all

theorem shbK4PathSupported_0123_iff
    {E A : Finset shbK4Edge} (p : (shbK4Graph E).Path 0 3)
    (hp : p.1.support = [(0 : Fin 4), 1, 2, 3]) :
    shbK4PathSupported A p ↔
      ({shbK4Edge.e01, shbK4Edge.e12, shbK4Edge.e23} :
        Finset shbK4Edge) ⊆ A := by
  have hedges : p.1.edges =
      [shbK4Edge.e01.code, shbK4Edge.e12.code, shbK4Edge.e23.code] := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support, hp]
    decide
  unfold shbK4PathSupported
  rw [hedges]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    shbK4Edge_code_mem_image_iff, shbK4Edge_forall_eq_code_mem_image_iff,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]

theorem shbK4PathSupported_013_iff
    {E A : Finset shbK4Edge} (p : (shbK4Graph E).Path 0 3)
    (hp : p.1.support = [(0 : Fin 4), 1, 3]) :
    shbK4PathSupported A p ↔
      ({shbK4Edge.e01, shbK4Edge.e13} : Finset shbK4Edge) ⊆ A := by
  have hedges : p.1.edges =
      [shbK4Edge.e01.code, shbK4Edge.e13.code] := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support, hp]
    decide
  unfold shbK4PathSupported
  rw [hedges]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    shbK4Edge_code_mem_image_iff, shbK4Edge_forall_eq_code_mem_image_iff,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]

theorem shbK4PathSupported_0213_iff
    {E A : Finset shbK4Edge} (p : (shbK4Graph E).Path 0 3)
    (hp : p.1.support = [(0 : Fin 4), 2, 1, 3]) :
    shbK4PathSupported A p ↔
      ({shbK4Edge.e02, shbK4Edge.e12, shbK4Edge.e13} :
        Finset shbK4Edge) ⊆ A := by
  have hedges : p.1.edges =
      [shbK4Edge.e02.code, shbK4Edge.e12.code, shbK4Edge.e13.code] := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support, hp]
    decide
  unfold shbK4PathSupported
  rw [hedges]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    shbK4Edge_code_mem_image_iff, shbK4Edge_forall_eq_code_mem_image_iff,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]

theorem shbK4PathSupported_023_iff
    {E A : Finset shbK4Edge} (p : (shbK4Graph E).Path 0 3)
    (hp : p.1.support = [(0 : Fin 4), 2, 3]) :
    shbK4PathSupported A p ↔
      ({shbK4Edge.e02, shbK4Edge.e23} : Finset shbK4Edge) ⊆ A := by
  have hedges : p.1.edges =
      [shbK4Edge.e02.code, shbK4Edge.e23.code] := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support, hp]
    decide
  unfold shbK4PathSupported
  rw [hedges]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    shbK4Edge_code_mem_image_iff, shbK4Edge_forall_eq_code_mem_image_iff,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]

theorem shbK4DirectPath_supported_iff
    (E A : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E) :
    shbK4PathSupported A (shbK4DirectPath E h03) ↔
      shbK4Edge.e03 ∈ A := by
  have hedges : (shbK4DirectPath E h03).1.edges =
      [shbK4Edge.e03.code] := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support,
      shbK4DirectPath_support]
    decide
  unfold shbK4PathSupported
  rw [hedges]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    shbK4Edge_code_mem_image_iff]

theorem shbK4Graph_adj_of_edge
    (E : Finset shbK4Edge) (k : shbK4Edge) (hk : k ∈ E)
    {x y : Fin 4} (hcode : k.code = s(x, y)) (hne : x ≠ y) :
    (shbK4Graph E).Adj x y := by
  rw [shbK4Graph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨Finset.mem_image.mpr ⟨k, hk, hcode⟩, hne⟩

end StatMech.Sharpness
