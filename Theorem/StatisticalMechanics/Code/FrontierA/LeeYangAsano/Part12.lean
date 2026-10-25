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
import Def.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part11
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

@[simp] theorem leeYangAnchor_mem_choiceSupport
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool)) (v : V) :
    leeYangAnchor G v ∈ leeYangChoiceSupport G x ↔ x.1 v = true := by
  simp [leeYangChoiceSupport, leeYangChoiceSelected, leeYangAnchor]

@[simp] theorem leeYangHalf0_mem_choiceSupport
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool))
    (e : ↑G.edgeFinset) :
    leeYangHalf G (leeYangEndpoint0 G e) e ∈ leeYangChoiceSupport G x ↔
      (x.2 e).1 = true := by
  simp [leeYangChoiceSupport, leeYangChoiceSelected, leeYangHalf]

@[simp] theorem leeYangHalf1_mem_choiceSupport
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool))
    (e : ↑G.edgeFinset) :
    leeYangHalf G (leeYangEndpoint1 G e) e ∈ leeYangChoiceSupport G x ↔
      (x.2 e).2 = true := by
  simp [leeYangChoiceSupport, leeYangChoiceSelected, leeYangHalf,
    Ne.symm (leeYang_endpoints_ne G e)]

theorem leeYang_incidence_pair_mem (e : ↑G.edgeFinset) (v : V) :
    (v, e) ∈ leeYangIncidenceFinset G ↔ v ∈ e.1 := by
  simp [leeYangIncidenceFinset]

theorem leeYangChoiceSupport_consistent_iff
    (sigma : V → Bool) (tau : ↑G.edgeFinset → Bool × Bool) :
    LeeYangConsistent G (leeYangIncidenceFinset G).toList
        (leeYangChoiceSupport G (sigma, tau)) ↔
      tau = leeYangTauOf G sigma := by
  constructor
  · intro h
    funext e
    apply Prod.ext
    · have hmem : (leeYangEndpoint0 G e, e) ∈
          (leeYangIncidenceFinset G).toList := by
        rw [Finset.mem_toList, leeYang_incidence_pair_mem]
        exact Sym2.out_fst_mem e.1
      have hc := h _ hmem
      simp only [leeYangAnchor_mem_choiceSupport,
        leeYangHalf0_mem_choiceSupport] at hc
      exact Bool.eq_iff_iff.mpr hc.symm
    · have hmem : (leeYangEndpoint1 G e, e) ∈
          (leeYangIncidenceFinset G).toList := by
        rw [Finset.mem_toList, leeYang_incidence_pair_mem]
        exact Sym2.out_snd_mem e.1
      have hc := h _ hmem
      simp only [leeYangAnchor_mem_choiceSupport,
        leeYangHalf1_mem_choiceSupport] at hc
      exact Bool.eq_iff_iff.mpr hc.symm
  · intro htau p hp
    rcases p with ⟨v, e⟩
    rw [Finset.mem_toList, leeYang_incidence_pair_mem] at hp
    rw [htau]
    have hv : v = leeYangEndpoint0 G e ∨ v = leeYangEndpoint1 G e := by
      rw [← leeYang_endpoints_mk G e] at hp
      simpa using hp
    rcases hv with rfl | rfl
    · simp [leeYangTauOf]
    · simp [leeYangTauOf]

theorem mem_leeYangEraseHalves (L : List (V × ↑G.edgeFinset))
    (S : Finset (LeeYangVar G)) (k : LeeYangVar G) :
    k ∈ leeYangEraseHalves G L S ↔
      k ∈ S ∧ ∀ x ∈ L, k ≠ leeYangHalf G x.1 x.2 := by
  induction L generalizing S with
  | nil => simp [leeYangEraseHalves]
  | cons x L ih =>
      simp only [leeYangEraseHalves, List.foldl_cons]
      change k ∈ leeYangEraseHalves G L (S.erase (leeYangHalf G x.1 x.2)) ↔ _
      rw [ih]
      simp only [Finset.mem_erase, List.mem_cons, forall_eq_or_imp]
      aesop

end StatMech.FrontierA
