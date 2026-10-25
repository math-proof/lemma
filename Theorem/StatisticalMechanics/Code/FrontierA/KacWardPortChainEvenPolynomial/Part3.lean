/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


@[simp] theorem kwFinsetDartEdgeBits_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (Sym2 V)) (d : G.Dart) :
    (kwFinsetDartEdgeBits G F).1 d = (if d.edge ∈ F then 1 else 0) :=
  rfl

theorem kwDartEdgeBitsFinset_finset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    kwDartEdgeBitsFinset G (kwFinsetDartEdgeBits G F) = F := by
  ext edge
  induction edge using Sym2.ind with
  | _ v w =>
    constructor
    · simp only [kwDartEdgeBitsFinset, Finset.mem_filter]
      intro h
      have hvw : G.Adj v w := by simpa using h.1
      simpa [kwDartEdgeBitValue, hvw] using h.2
    · intro hedge
      have hgraph := hF hedge
      simp only [kwDartEdgeBitsFinset, Finset.mem_filter]
      refine ⟨hgraph, ?_⟩
      have hvw : G.Adj v w := by simpa using hgraph
      simp [kwDartEdgeBitValue, hvw, hedge]

theorem kwFinsetDartEdgeBits_bitsFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) :
    kwFinsetDartEdgeBits G (kwDartEdgeBitsFinset G b) = b := by
  apply Subtype.ext
  funext d
  simp only [kwFinsetDartEdgeBits_apply, mem_kwDartEdgeBitsFinset_iff]
  have h : b.1 d = 0 ∨ b.1 d = 1 := by omega
  rcases h with h | h <;> simp [h]


theorem kw_incidenceFinset_eq_image_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.incidenceFinset v = (G.neighborFinset v).image (fun w => s(v, w)) := by
  ext edge
  induction edge using Sym2.inductionOn with
  | _ a b =>
      simp only [SimpleGraph.mem_incidenceFinset,
        SimpleGraph.mk'_mem_incidenceSet_iff, Finset.mem_image,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hab, rfl | rfl⟩
        · exact ⟨b, hab, rfl⟩
        · exact ⟨a, hab.symm, Sym2.eq_swap⟩
      · rintro ⟨w, hvw, heq⟩
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨hva, hwb⟩ | ⟨hvb, hwa⟩
        · subst a
          subst b
          exact ⟨hvw, Or.inl rfl⟩
        · subst a
          subst b
          exact ⟨hvw.symm, Or.inr rfl⟩

theorem kw_neighborEdge_injective
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (v : V) :
    Set.InjOn (fun w => s(v, w)) (G.neighborSet v) := by
  intro a ha b hb heq
  rw [Sym2.eq_iff] at heq
  rcases heq with h | h
  · exact h.2
  · exfalso
    have hva : G.Adj v a := ha
    rw [h.2] at hva
    exact G.loopless.irrefl v hva

theorem kw_incCount_filter_edgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : Sym2 V → Prop) [DecidablePred Q] (v : V) :
    incCount (G.edgeFinset.filter Q) v =
      ((G.incidenceFinset v).filter Q).card := by
  unfold incCount
  rw [SimpleGraph.incidenceFinset_eq_filter]
  congr 1
  ext edge
  simp only [Finset.mem_filter]
  tauto

theorem kw_cast_incCount_filter_eq_neighbor_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : Sym2 V → Prop) [DecidablePred Q] (v : V) :
    ((incCount (G.edgeFinset.filter Q) v : ℕ) : ZMod 2) =
      ∑ w ∈ G.neighborFinset v,
        if Q s(v, w) then (1 : ZMod 2) else 0 := by
  rw [kw_incCount_filter_edgeFinset, Finset.natCast_card_filter,
    kw_incidenceFinset_eq_image_neighborFinset, Finset.sum_image]
  intro a ha b hb hab
  apply kw_neighborEdge_injective G v
  · exact (SimpleGraph.mem_neighborFinset G v a).mp ha
  · exact (SimpleGraph.mem_neighborFinset G v b).mp hb
  · exact hab

@[simp] theorem kw_fin2_indicator_eq (a : Fin 2) :
    (if a = 1 then (1 : Fin 2) else 0) = a := by
  have h : a = 0 ∨ a = 1 := by omega
  rcases h with h | h <;> simp [h]

@[simp] theorem kw_zmod2_indicator_eq (a : Fin 2) :
    (if a = 1 then (1 : ZMod 2) else 0) = a := by
  fin_cases a <;> decide


end StatMech.FrontierA
