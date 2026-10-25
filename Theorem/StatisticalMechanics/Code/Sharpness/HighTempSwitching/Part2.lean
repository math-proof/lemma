/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSources.Part3
import Def.StatisticalMechanics.Code.Sharpness.HighTempSwitching
open Finset
open scoped symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


@[simp]
theorem sourcePair_self (a : V) : sourcePair a a = ∅ := by
  simp [sourcePair]

theorem sourcePair_eq_pair {a b : V} (hab : a ≠ b) :
    sourcePair a b = {a, b} := by
  ext v
  simp only [sourcePair, Finset.mem_symmDiff, Finset.mem_singleton,
    Finset.mem_insert]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, hab⟩
    · exact Or.inr ⟨rfl, hab.symm⟩


theorem sourcePair_chain (a b c d : V) :
    sourcePair a b ∆ sourcePair b c ∆ sourcePair c d = sourcePair a d := by
  ext v
  simp only [sourcePair, Finset.mem_symmDiff, Finset.mem_singleton]
  tauto


theorem hasOddBoundary_path_edges {K : SimpleGraph V} {a b : V}
    (p : K.Walk a b) (hp : p.IsPath) :
    HasOddBoundary p.edges.toFinset (sourcePair a b) := by
  intro v
  have hdeg : incCount p.edges.toFinset v = walkDeg p v := by
    unfold incCount walkDeg
    have hfilter :
        p.edges.toFinset.filter (fun e => v ∈ e) =
          (p.edges.filter (fun e => decide (v ∈ e))).toFinset := by
      ext e
      simp
    rw [hfilter]
    exact List.toFinset_card_of_nodup (hp.edges_nodup.filter _)
  rw [hdeg, walkDeg_odd_iff p hp v]
  simp only [sourcePair, Finset.mem_symmDiff, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl, hab⟩
    · exact Or.inl ⟨rfl, hab⟩
    · exact Or.inr ⟨rfl, hab.symm⟩
  · rintro (⟨hva, hvb⟩ | ⟨hvb, hva⟩)
    · exact ⟨Or.inl hva, fun hab => hvb (hva.trans hab)⟩
    · exact ⟨Or.inr hvb, fun hab => hva (hvb.trans hab.symm)⟩


theorem walk_edge_getElem {K : SimpleGraph V} {a b : V}
    (p : K.Walk a b) (i : ℕ) (hi : i < p.length) :
    p.edges[i]'(by rw [SimpleGraph.Walk.length_edges]; exact hi) =
      s(p.getVert i, p.getVert (i + 1)) := by
  induction p generalizing i with
  | nil => simp at hi
  | cons hadj q ih =>
      cases i with
      | zero =>
          simp only [SimpleGraph.Walk.edges_cons, List.getElem_cons_zero,
            SimpleGraph.Walk.getVert_zero]
          congr 1
          rw [SimpleGraph.Walk.getVert_cons_succ,
            SimpleGraph.Walk.getVert_zero]
      | succ n =>
          simp only [SimpleGraph.Walk.edges_cons, List.getElem_cons_succ]
          rw [SimpleGraph.Walk.length_cons] at hi
          rw [ih n (by omega), SimpleGraph.Walk.getVert_cons_succ,
            SimpleGraph.Walk.getVert_cons_succ]


theorem sourcePair_symmDiff_firstExit
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F H : Finset (Sym2 V)) {o z : V}
    (hFsub : F ⊆ G.edgeFinset) (hHsub : H ⊆ G.edgeFinset)
    (hoz : o ≠ z) (hF : HasOddBoundary F (sourcePair o z))
    (hH : HasOddBoundary H ∅) (S : Finset V) (ho : o ∈ S) (hz : z ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, ∃ Q : Finset (Sym2 V),
      Q ⊆ F ∆ H ∧ HasOddBoundary Q (sourcePair o x) ∧
        s(x, y) ∉ Q ∧ s(x, y) ∈ F ∆ H := by
  have hUsub : F ∆ H ⊆ G.edgeFinset := by
    intro e he
    simp only [Finset.mem_symmDiff] at he
    rcases he with ⟨heF, _⟩ | ⟨heH, _⟩
    · exact hFsub heF
    · exact hHsub heH
  have hU0 := hasOddBoundary_symmDiff hF hH
  have hU : HasOddBoundary (F ∆ H) (sourcePair o z) := by
    convert hU0 using 1
    ext v
    simp only [sourcePair, Finset.mem_symmDiff, Finset.mem_singleton]
    tauto
  have hUpair : HasOddBoundary (F ∆ H) {o, z} := by
    rw [← sourcePair_eq_pair hoz]
    exact hU
  let p := (hasOddBoundary_backbone G (F ∆ H) hUsub hoz hUpair).some
  obtain ⟨k, hk1, hkle, hx, hy, _, hodd, _, _⟩ :=
    backbone_firstExit G p S ho hz
  let x := p.1.getVert (k - 1)
  let y := p.1.getVert k
  let Q := (p.1.take (k - 1)).edges.toFinset
  have hQbd : HasOddBoundary Q (sourcePair o x) := by
    exact hasOddBoundary_path_edges (p.1.take (k - 1)) (p.2.take (k - 1))
  have hQsub : Q ⊆ F ∆ H := by
    intro e he
    have heTake : e ∈ (p.1.take (k - 1)).edges := by
      exact List.mem_toFinset.mp he
    have hePath : e ∈ p.1.edges := by
      rw [SimpleGraph.Walk.edges_take] at heTake
      exact List.mem_of_mem_take heTake
    have heOdd := isBackbonePath_edge_odd G p hePath
    by_contra heU
    simp [edgeIndicatorCurrent, heU] at heOdd
  have heQ : s(x, y) ∉ Q := by
    intro he
    have heTake : s(x, y) ∈ List.take (k - 1) p.1.edges := by
      rw [← SimpleGraph.Walk.edges_take]
      exact List.mem_toFinset.mp he
    have hlenE : k - 1 < p.1.edges.length := by
      rw [SimpleGraph.Walk.length_edges]
      omega
    have hedge :
        s(x, y) = p.1.edges[k - 1]'hlenE := by
      have h := walk_edge_getElem p.1 (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at h
      exact h.symm
    have heDrop : s(x, y) ∈ List.drop (k - 1) p.1.edges := by
      rw [List.drop_eq_getElem_cons hlenE, ← hedge]
      exact List.mem_cons_self
    exact List.disjoint_take_drop p.2.edges_nodup (le_refl (k - 1)) heTake heDrop
  have heU : s(x, y) ∈ F ∆ H := by
    by_contra he
    simp [x, y, edgeIndicatorCurrent, he] at hodd
  exact ⟨x, hx, y, hy, Q, hQsub, hQbd, heQ, heU⟩


theorem erase_eq_symmDiff_singleton {α : Type*} [DecidableEq α]
    (F : Finset α) {e : α} (he : e ∈ F) :
    F.erase e = F ∆ {e} := by
  ext x
  rw [mem_symmDiff_singleton_iff]
  by_cases hxe : x = e
  · subst x
    simp [he]
  · simp [hxe]


theorem card_switch_erase_exit {α : Type*} [DecidableEq α]
    (F H Q : Finset α) {e : α} (hQ : Q ⊆ F ∆ H)
    (heF : e ∈ F) (heQ : e ∉ Q) :
    (H ∆ Q).card + ((F ∆ Q).erase e).card + 1 = F.card + H.card := by
  have heToggle : e ∈ F ∆ Q := by
    simp only [Finset.mem_symmDiff]
    exact Or.inl ⟨heF, heQ⟩
  have hcard := card_pair_symmDiff_eq F H Q hQ
  have herase := card_erase_of_mem heToggle
  have hpos : 0 < (F ∆ Q).card := card_pos.mpr ⟨e, heToggle⟩
  omega


theorem hasOddBoundary_singleton_sourcePair {x y : V} (hxy : x ≠ y) :
    HasOddBoundary ({s(x, y)} : Finset (Sym2 V)) (sourcePair x y) := by
  rw [hasOddBoundary_iff_srcP, sourcePair_eq_pair hxy]
  exact srcP_singleton s(x, y) x y rfl hxy


theorem hasOddBoundary_switch_erase_exit
    {F H Q : Finset (Sym2 V)} {o x y z : V}
    (hF : HasOddBoundary F (sourcePair o z))
    (hH : HasOddBoundary H ∅)
    (hQ : HasOddBoundary Q (sourcePair o x))
    (hxy : x ≠ y) (heF : s(x, y) ∈ F) (heQ : s(x, y) ∉ Q) :
    HasOddBoundary (H ∆ Q) (sourcePair o x) ∧
      HasOddBoundary ((F ∆ Q).erase s(x, y)) (sourcePair y z) := by
  have hleft := hasOddBoundary_symmDiff hH hQ
  have heToggle : s(x, y) ∈ F ∆ Q := by
    simp only [Finset.mem_symmDiff]
    exact Or.inl ⟨heF, heQ⟩
  have hright0 := hasOddBoundary_symmDiff hF hQ
  have hedge := hasOddBoundary_singleton_sourcePair (V := V) hxy
  have hright1 := hasOddBoundary_symmDiff hright0 hedge
  constructor
  · have hempty : (∅ : Finset V) ∆ sourcePair o x = sourcePair o x := by
      ext v
      simp [Finset.mem_symmDiff]
    rw [hempty] at hleft
    exact hleft
  · rw [erase_eq_symmDiff_singleton (F ∆ Q) heToggle]
    convert hright1 using 1
    ext v
    simp only [sourcePair, Finset.mem_symmDiff, Finset.mem_singleton]
    tauto


end Sharpness
end StatMech
