/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Def.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part4
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jce_edgeFlip_symm (E : Finset (Sym2 (Site 2))) : wcl_SymmFlip (jce_edgeFlip E) := by
  intro a b hab
  unfold jce_edgeFlip
  rw [sharedPrimalEdge_comm_of_adj hab]


theorem jce_edgeFlip_compat (hres : jce_HorizStepResidue) (E : Finset (Sym2 (Site 2)))
    (hcc : jce_ClosedContour (E : Set (Sym2 (Site 2)))) :
    ∀ a b, (hypercubicLattice 2).Adj a b →
      (jce_edgeFlip E a b ↔ (jce_phi E a ↔ ¬ jce_phi E b)) := by
  intro a b hab
  have := jce_phi_compat hres E hcc a b hab
  rwa [Finset.mem_coe] at this


theorem jce_edgeFlip_closedEven (hres : jce_HorizStepResidue) (E : Finset (Sym2 (Site 2)))
    (hcc : jce_ClosedContour (E : Set (Sym2 (Site 2)))) :
    wcl_ClosedEven (jce_edgeFlip E) :=
  wcl_closedEven_of_compat (jce_edgeFlip E) (jce_phi E) (jce_edgeFlip_compat hres E hcc)


theorem jce_sharedPrimalEdge_inj {a b c d : Site 2} (hab : (hypercubicLattice 2).Adj a b)
    (hcd : (hypercubicLattice 2).Adj c d) :
    (s(a, b) = s(c, d) ↔ sharedPrimalEdge a b = sharedPrimalEdge c d) := by
  constructor
  · intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact sharedPrimalEdge_comm_of_adj hab
  · intro h
    have ha : a = ![a 0, a 1] := by funext i; fin_cases i <;> rfl
    have hb : b = ![b 0, b 1] := by funext i; fin_cases i <;> rfl
    have hc : c = ![c 0, c 1] := by funext i; fin_cases i <;> rfl
    have hd : d = ![d 0, d 1] := by funext i; fin_cases i <;> rfl
    have hab' := hab; have hcd' := hcd
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hab' hcd'
    rw [ha, hb, hc, hd] at h ⊢
    unfold sharedPrimalEdge at h
    by_cases h1 : a 0 = b 0 <;> by_cases h2 : c 0 = d 0 <;>
      simp only [h1, h2, if_true, if_false, Matrix.cons_val_zero, Matrix.cons_val_one,
        Sym2.eq_iff, whc_site_eq_iff] at h ⊢ <;> omega


theorem jce_cutFlip_eq_edgeFlip (H : SimpleGraph (Site 2)) [Fintype H.edgeSet]
    (f0 g0 : Site 2) (hfg : (hypercubicLattice 2).Adj f0 g0) {a b : Site 2}
    (hab : (hypercubicLattice 2).Adj a b) :
    (wcl_cutFlip H f0 g0 a b ↔
      jce_edgeFlip (insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset) a b) := by
  unfold wcl_cutFlip whc_isCross jce_edgeFlip
  rw [Finset.mem_insert, Set.mem_toFinset]
  have hsy : sharedPrimalEdge b a = sharedPrimalEdge a b :=
    (sharedPrimalEdge_comm_of_adj hab).symm
  rw [hsy]
  rw [jce_sharedPrimalEdge_inj hab hfg]
  tauto


theorem jce_flipCount_congr (flip flip' : Site 2 → Site 2 → Prop)
    (hagree : ∀ a b, (hypercubicLattice 2).Adj a b → (flip a b ↔ flip' a b))
    {x y : Site 2} (w : (hypercubicLattice 2).Walk x y) :
    wcl_flipCount flip w = wcl_flipCount flip' w := by
  induction w with
  | nil => rw [wcl_flipCount_nil, wcl_flipCount_nil]
  | @cons a b c hab p ih =>
    rw [wcl_flipCount_cons, wcl_flipCount_cons, ih]
    have h1 := hagree a b hab
    have h2 := hagree b a hab.symm
    by_cases hf : flip a b ∨ flip b a
    · rw [if_pos hf, if_pos (by tauto)]
    · rw [if_neg hf, if_neg (by tauto)]


theorem jce_closedEven_congr (flip flip' : Site 2 → Site 2 → Prop)
    (hagree : ∀ a b, (hypercubicLattice 2).Adj a b → (flip a b ↔ flip' a b))
    (hce : wcl_ClosedEven flip') : wcl_ClosedEven flip := by
  intro x w
  rw [jce_flipCount_congr flip flip' hagree w]
  exact hce w


theorem jce_cutFlip_closedEven (hres : jce_HorizStepResidue) (H : SimpleGraph (Site 2))
    [Fintype H.edgeSet] (f0 g0 : Site 2) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))) :
    wcl_ClosedEven (wcl_cutFlip H f0 g0) := by
  set E := insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset with hE
  apply jce_closedEven_congr (wcl_cutFlip H f0 g0) (jce_edgeFlip E)
    (fun a b hab => jce_cutFlip_eq_edgeFlip H f0 g0 hfg hab)
  exact jce_edgeFlip_closedEven hres E hcc


theorem jce_whitney_forward_of_evenDegree (hres : jce_HorizStepResidue) (H : SimpleGraph (Site 2))
    [Fintype H.edgeSet] (p q f0 g0 : Site 2) (hpq : (hypercubicLattice 2).Adj p q)
    (hnpq : s(p, q) ∉ H.edgeSet) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))) :
    ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 :=
  wcl_whitney_forward_of_closedEven H p q f0 g0 hpq hnpq hfg hshared
    (jce_cutFlip_closedEven hres H f0 g0 hfg hcc)


theorem jce_cutFlip_closedEven' (H : SimpleGraph (Site 2)) [Fintype H.edgeSet]
    (f0 g0 : Site 2) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))) :
    wcl_ClosedEven (wcl_cutFlip H f0 g0) :=
  jce_cutFlip_closedEven jce_horizStepResidue_holds H f0 g0 hfg hcc


theorem jce_discreteJordanFaithful_of_evenDegree (H : SimpleGraph (Site 2)) [Fintype H.edgeSet]
    (p q f0 g0 : Site 2) (hpq : (hypercubicLattice 2).Adj p q)
    (hnpq : s(p, q) ∉ H.edgeSet) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))) :
    ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 :=
  jce_whitney_forward_of_evenDegree jce_horizStepResidue_holds H p q f0 g0 hpq hnpq hfg hshared hcc


theorem jce_empty_closedContour :
    jce_ClosedContour ((∅ : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))) := by
  classical
  intro v
  unfold jce_degree jce_nbr
  rw [Nat.even_iff, Finset.card_filter, Fin.sum_univ_four]
  simp only [Finset.mem_coe, Finset.notMem_empty, if_false, add_zero]


theorem jce_empty_closedEven :
    wcl_ClosedEven (jce_edgeFlip (∅ : Finset (Sym2 (Site 2)))) :=
  jce_edgeFlip_closedEven jce_horizStepResidue_holds ∅ jce_empty_closedContour


theorem jce_singleEdge_not_closedContour :
    ¬ jce_ClosedContour
      (({s(![(0:ℤ), 0], ![1, 0])} : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))) := by
  classical
  intro h
  have hd := h ![(0:ℤ), 0]
  unfold jce_degree jce_nbr at hd
  simp only [Finset.mem_coe, Finset.mem_singleton, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hd
  rw [Nat.even_iff, Finset.card_filter, Fin.sum_univ_four] at hd
  simp only [Sym2.eq_iff, whc_site_eq_iff, Matrix.cons_val_zero, Matrix.cons_val_one] at hd
  norm_num at hd


end Lattice
end StatMech
