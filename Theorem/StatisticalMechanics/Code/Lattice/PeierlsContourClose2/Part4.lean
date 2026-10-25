/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsEulerParity
import Def.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable


@[simp] theorem flankFacesSym_mk (p q : Site 2) : flankFacesSym s(p, q) = flankFaces p q := rfl


theorem adj_cases {f g : Site 2} (h : (hypercubicLattice 2).Adj f g) :
    (f 0 = g 0 ∧ (f 1 = g 1 + 1 ∨ g 1 = f 1 + 1)) ∨
    (f 1 = g 1 ∧ (f 0 = g 0 + 1 ∨ g 0 = f 0 + 1)) := by
  have hadj := h
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  by_cases h0 : f 0 = g 0
  · left; refine ⟨h0, ?_⟩
    have : (f 1 - g 1).natAbs = 1 := by omega
    rcases Int.natAbs_eq_iff.mp this with he | he <;> omega
  · right
    have h1 : f 1 = g 1 := by
      by_contra hne
      have hb1 : (f 1 - g 1).natAbs ≥ 1 := by omega
      have hb0 : (f 0 - g 0).natAbs ≥ 1 := by
        rcases Int.natAbs_eq (f 0 - g 0) with he | he <;> omega
      omega
    refine ⟨h1, ?_⟩
    have : (f 0 - g 0).natAbs = 1 := by omega
    rcases Int.natAbs_eq_iff.mp this with he | he <;> omega


theorem cons_eq_site {f : Site 2} {a b : ℤ} (ha : a = f 0) (hb : b = f 1) : ![a, b] = f := by
  subst ha hb; funext i; fin_cases i <;> simp


theorem flankFacesSym_symPrimal {f g : Site 2} (h : (hypercubicLattice 2).Adj f g) :
    flankFacesSym (symPrimal f g) = s(f, g) := by
  classical
  rcases adj_cases h with ⟨h0, hy⟩ | ⟨h1, hx⟩
  · have hsp : symPrimal f g = s(![f 0, max (f 1) (g 1)], ![f 0 + 1, max (f 1) (g 1)]) := by
      unfold symPrimal; rw [if_pos h0]
    rw [hsp, flankFacesSym_mk]
    unfold flankFaces
    rw [if_neg (by simp only [Matrix.cons_val_zero]; omega)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show min (f 0) (f 0 + 1) = f 0 by omega, min_self]
    rcases hy with hfg | hgf
    · rw [show max (f 1) (g 1) = f 1 by omega, show f 1 - 1 = g 1 by omega, Sym2.eq_swap]
      rw [cons_eq_site rfl rfl, cons_eq_site h0 (by omega)]
    · rw [show max (f 1) (g 1) = g 1 by omega, show g 1 - 1 = f 1 by omega]
      rw [cons_eq_site rfl rfl, cons_eq_site h0 rfl]
  · have hsp : symPrimal f g
        = s(![max (f 0) (g 0), min (f 1) (g 1)], ![max (f 0) (g 0), min (f 1) (g 1) + 1]) := by
      unfold symPrimal; rw [if_neg (by rw [h1] at *; intro hc; omega)]
    rw [hsp, flankFacesSym_mk]
    unfold flankFaces
    rw [if_pos (by simp only [Matrix.cons_val_zero])]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show min (min (f 1) (g 1)) (min (f 1) (g 1) + 1) = min (f 1) (g 1) by omega, h1, min_self]
    rcases hx with hfg | hgf
    · rw [show max (f 0) (g 0) = f 0 by omega, show f 0 - 1 = g 0 by omega, Sym2.eq_swap]
      rw [cons_eq_site rfl h1.symm, cons_eq_site rfl rfl]
    · rw [show max (f 0) (g 0) = g 0 by omega, show g 0 - 1 = f 0 by omega]
      rw [cons_eq_site rfl h1.symm, cons_eq_site rfl rfl]


theorem symPrimalSym_flankFaces {p q : Site 2} (h : (hypercubicLattice 2).Adj p q) :
    symPrimalSym (flankFaces p q) = s(p, q) := by
  classical
  rcases adj_cases h with ⟨h0, hy⟩ | ⟨h1, hx⟩
  · have hfl : flankFaces p q = s(![p 0 - 1, min (p 1) (q 1)], ![p 0, min (p 1) (q 1)]) := by
      unfold flankFaces; rw [if_pos h0]
    rw [hfl, symPrimalSym_mk]; unfold symPrimal
    rw [if_neg (by simp only [Matrix.cons_val_zero]; omega)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show max (p 0 - 1) (p 0) = p 0 by omega, min_self]
    rcases hy with hpq | hqp
    · rw [show min (p 1) (q 1) = q 1 by omega, show q 1 + 1 = p 1 by omega, Sym2.eq_swap]
      rw [cons_eq_site rfl rfl, cons_eq_site h0 rfl]
    · rw [show min (p 1) (q 1) = p 1 by omega, show p 1 + 1 = q 1 by omega]
      rw [cons_eq_site rfl rfl, cons_eq_site h0 rfl]
  · have hfl : flankFaces p q
        = s(![min (p 0) (q 0), min (p 1) (q 1) - 1], ![min (p 0) (q 0), min (p 1) (q 1)]) := by
      unfold flankFaces; rw [if_neg (by rw [h1] at *; intro hc; omega)]
    rw [hfl, symPrimalSym_mk]; unfold symPrimal
    rw [if_pos (by simp only [Matrix.cons_val_zero])]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show max (min (p 1) (q 1) - 1) (min (p 1) (q 1)) = min (p 1) (q 1) by omega, h1, min_self]
    rcases hx with hpq | hqp
    · rw [show min (p 0) (q 0) = q 0 by omega, show q 0 + 1 = p 0 by omega, Sym2.eq_swap]
      rw [cons_eq_site rfl h1.symm, cons_eq_site rfl rfl]
    · rw [show min (p 0) (q 0) = p 0 by omega, show p 0 + 1 = q 0 by omega]
      rw [cons_eq_site rfl h1.symm, cons_eq_site rfl rfl]


theorem flankFaces_latAdj {p q : Site 2} (h : (hypercubicLattice 2).Adj p q) :
    ∃ f g : Site 2, flankFaces p q = s(f, g) ∧ (hypercubicLattice 2).Adj f g := by
  classical
  rcases adj_cases h with ⟨h0, _⟩ | ⟨h1, _⟩
  · refine ⟨![p 0 - 1, min (p 1) (q 1)], ![p 0, min (p 1) (q 1)], ?_, ?_⟩
    · unfold flankFaces; rw [if_pos h0]
    · have h2 := (latAdj_left (p 0) (min (p 1) (q 1))).symm
      convert h2 using 2
  · refine ⟨![min (p 0) (q 0), min (p 1) (q 1) - 1], ![min (p 0) (q 0), min (p 1) (q 1)], ?_, ?_⟩
    · unfold flankFaces; rw [if_neg (by rw [h1] at *; intro hc; omega)]
    · have h2 := (latAdj_bottom (min (p 0) (q 0)) (min (p 1) (q 1))).symm
      convert h2 using 2


theorem flankFacesSym_mem_edgeSet {K : Set (Site 2)} {e : Sym2 (Site 2)}
    (he : e ∈ boundaryEdgeSet K) :
    flankFacesSym e ∈ (faceBoundaryGraph K).edgeSet ∧ symPrimalSym (flankFacesSym e) = e := by
  classical
  obtain ⟨hedge, hstr⟩ := he
  induction e with
  | h p q =>
    rw [SimpleGraph.mem_edgeSet] at hedge
    obtain ⟨f, g, hfg, hfgadj⟩ := flankFaces_latAdj hedge
    rw [flankFacesSym_mk]
    have hsps : symPrimalSym (flankFaces p q) = s(p, q) := symPrimalSym_flankFaces hedge
    refine ⟨?_, hsps⟩
    rw [hfg, SimpleGraph.mem_edgeSet, faceBoundaryGraph_adj_iff_boundaryEdgeSet]
    refine ⟨hfgadj, ?_⟩
    
    have : sharedPrimalEdge f g = s(p, q) := by
      rw [← symPrimal_eq_shared hfgadj, ← symPrimalSym_mk, ← hfg, hsps]
    rw [this]
    exact ⟨hedge, hstr⟩


theorem symPrimalSym_mem_boundaryEdgeSet {K : Set (Site 2)} {e : Sym2 (Site 2)}
    (he : e ∈ (faceBoundaryGraph K).edgeSet) : symPrimalSym e ∈ boundaryEdgeSet K := by
  classical
  induction e with
  | h f g =>
    rw [SimpleGraph.mem_edgeSet] at he
    rw [symPrimalSym_mk, symPrimal_eq_shared he.1]
    rw [faceBoundaryGraph_adj_iff_boundaryEdgeSet] at he
    exact he.2


theorem symPrimalSym_injOn_edges (K : Set (Site 2)) :
    Set.InjOn symPrimalSym ((faceBoundaryGraph K).edgeSet) := by
  intro e1 he1 e2 he2 heq
  induction e1 with
  | h f1 g1 => induction e2 with
    | h f2 g2 =>
      rw [SimpleGraph.mem_edgeSet] at he1 he2
      have hl1 : flankFacesSym (symPrimal f1 g1) = s(f1, g1) := flankFacesSym_symPrimal he1.1
      have hl2 : flankFacesSym (symPrimal f2 g2) = s(f2, g2) := flankFacesSym_symPrimal he2.1
      rw [symPrimalSym_mk, symPrimalSym_mk] at heq
      rw [← hl1, ← hl2, heq]


end Lattice
end StatMech
