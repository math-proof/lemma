/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part14
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


theorem kwg_primal_incident_iff_mem (P : PlanarZ2Subgraph) (e : kwg_Edge P) (x : P.V) :
    kwg_incidentMod2 x (kwg_primalEnds P e) ↔ x ∈ e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : u ≠ v := fun h => by
        subst v
        exact P.G.irrefl ((SimpleGraph.mem_edgeSet P.G).mp he)
      simp only [kwg_primalEnds, kwg_incidentMod2_mk, Sym2.mem_iff]
      constructor
      · rintro (⟨rfl, _⟩ | ⟨rfl, _⟩)
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact Or.inl ⟨rfl, huv.symm⟩
        · exact Or.inr ⟨rfl, huv⟩

@[simp] theorem kwg_mem_primalEdgeFinset (P : PlanarZ2Subgraph)
    (F : Finset (kwg_Edge P)) (e : kwg_Edge P) :
    e.1 ∈ kwg_primalEdgeFinset P F ↔ e ∈ F := by
  classical
  simp [kwg_primalEdgeFinset]


theorem kwg_sum_count_eq_countP {A : Type*} [DecidableEq A]
    (D : Finset A) (l : List A) :
    (∑ a ∈ D, l.count a) = l.countP (fun a => decide (a ∈ D)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.countP_cons]
      simp_rw [List.count_cons]
      rw [Finset.sum_add_distrib, ih]
      by_cases ha : a ∈ D
      · simp [ha]
      · simp [ha]


theorem kwg_dualEven_evenOnCycles (P : PlanarZ2Subgraph)
    (F : Finset (kwg_Edge P)) (hev : kwg_IsEven (kwg_dualEnds P) F) :
    EvenOnCycles P.G (kwg_primalEdgeFinset P F) := by
  classical
  letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
  intro x p
  have hs := kwg_even_split_card (kwg_dualEnds P) F (kwg_walkFaceColour P p) hev
  have hfilter :
      F.filter (fun e => kwg_isSplit (kwg_walkFaceColour P p) (kwg_dualEnds P e)) =
        F.filter (fun e => Odd (p.edges.count e.1)) := by
    apply Finset.filter_congr
    intro e _
    rw [kwg_walkFaceColour_split_iff_odd P p e]
    change Odd ((kwg_latticeWalk P p).edges.count (Sym2.map P.emb e.1)) ↔ _
    rw [kwg_latticeWalk_count P p e.1]
  rw [hfilter] at hs
  have hsum : Even (∑ e ∈ F, p.edges.count e.1) :=
    (kwg_even_sum_iff_even_odd_filter F (fun e => p.edges.count e.1)).mpr hs
  have hcount : Even
      (p.edges.countP (fun e => decide (e ∈ kwg_primalEdgeFinset P F))) := by
    rw [← kwg_sum_count_eq_countP (kwg_primalEdgeFinset P F) p.edges]
    rw [kwg_primalEdgeFinset, Finset.sum_map]
    exact hsum
  rw [kwg_walkParity_eq_decide_odd_countP]
  have hnot : ¬ Odd
      (p.edges.countP (fun e => decide (e ∈ kwg_primalEdgeFinset P F))) := by
    intro hodd
    obtain ⟨a, ha⟩ := hcount
    obtain ⟨b, hb⟩ := hodd
    omega
  rw [decide_eq_false hnot]


end Ising
end StatMech
