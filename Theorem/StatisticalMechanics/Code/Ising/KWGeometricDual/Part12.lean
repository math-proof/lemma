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
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part13
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


theorem kwg_walkFaceColour_split_iff_odd (P : PlanarZ2Subgraph) {x : P.V}
    (p : P.G.Walk x x) (e : kwg_Edge P) :
    kwg_isSplit (kwg_walkFaceColour P p) (kwg_dualEnds P e) ↔
      Odd ((kwg_latticeWalk P p).edges.count (kwg_embeddedEdge P e)) := by
  classical
  let R := whb_faceRegion (imageGraph P)
  let L := kwg_flankLeft P e
  let U := kwg_flankRight P e
  have hL : fwr_faceInside (kwg_latticeWalk P p)
      ((R.connectedComponentMk L).out) ↔
      fwr_faceInside (kwg_latticeWalk P p) L := by
    apply kwg_faceInside_eq_of_regionReachable P p
    exact ConnectedComponent.exact (R.connectedComponentMk L).out_eq
  have hU : fwr_faceInside (kwg_latticeWalk P p)
      ((R.connectedComponentMk U).out) ↔
      fwr_faceInside (kwg_latticeWalk P p) U := by
    apply kwg_faceInside_eq_of_regionReachable P p
    exact ConnectedComponent.exact (R.connectedComponentMk U).out_eq
  rw [kwg_dualEnds, kwg_isSplit_mk]
  simp only [kwg_walkFaceColour]
  change decide (fwr_faceInside (kwg_latticeWalk P p)
      ((R.connectedComponentMk L).out)) ≠
    decide (fwr_faceInside (kwg_latticeWalk P p)
      ((R.connectedComponentMk U).out)) ↔ _
  have hflip := fwr_faceCutFlip (kwg_latticeWalk P p) (kwg_flanks_adj P e)
  rw [kwg_flanks_shared P e] at hflip
  change (fwr_faceInside (kwg_latticeWalk P p) L ↔
    ¬ fwr_faceInside (kwg_latticeWalk P p) U) ↔ _ at hflip
  have hsides :
      (decide (fwr_faceInside (kwg_latticeWalk P p) ((R.connectedComponentMk L).out)) ≠
        decide (fwr_faceInside (kwg_latticeWalk P p) ((R.connectedComponentMk U).out))) ↔
      (fwr_faceInside (kwg_latticeWalk P p) L ↔
        ¬ fwr_faceInside (kwg_latticeWalk P p) U) := by
    by_cases hLo : fwr_faceInside (kwg_latticeWalk P p) ((R.connectedComponentMk L).out) <;>
      by_cases hUo : fwr_faceInside (kwg_latticeWalk P p) ((R.connectedComponentMk U).out) <;>
      by_cases hLf : fwr_faceInside (kwg_latticeWalk P p) L <;>
      by_cases hUf : fwr_faceInside (kwg_latticeWalk P p) U <;> simp_all
  exact hsides.trans hflip


theorem kwg_even_sum_iff_even_odd_filter {E : Type*} [DecidableEq E]
    (F : Finset E) (n : E → ℕ) :
    Even (∑ e ∈ F, n e) ↔ Even (F.filter (fun e => Odd (n e))).card := by
  classical
  have hne : (-1 : ℤ) ≠ 1 := by norm_num
  rw [← neg_one_pow_eq_one_iff_even hne, ← neg_one_pow_eq_one_iff_even hne]
  rw [← Finset.prod_pow_eq_pow_sum]
  have hprod : (∏ e ∈ F, (-1 : ℤ) ^ n e) =
      (-1 : ℤ) ^ (F.filter (fun e => Odd (n e))).card := by
    calc
      (∏ e ∈ F, (-1 : ℤ) ^ n e) =
          ∏ e ∈ F, if Odd (n e) then (-1 : ℤ) else 1 := by
            apply Finset.prod_congr rfl
            intro e _
            by_cases ho : Odd (n e)
            · rw [if_pos ho, ho.neg_one_pow]
            · rw [if_neg ho]
              exact Even.neg_one_pow ((Nat.even_or_odd (n e)).resolve_right ho)
      _ = (-1 : ℤ) ^ (F.filter (fun e => Odd (n e))).card := by
        rw [← Finset.prod_filter]
        simp
  rw [hprod]


theorem kwg_walkParity_eq_decide_odd_countP {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (D : Finset (Sym2 V)) {x y : V} (p : G.Walk x y) :
    walkParity G D p =
      decide (Odd (p.edges.countP (fun e => decide (e ∈ D)))) := by
  simp only [Nat.odd_iff]
  induction p with
  | nil => simp
  | @cons u v w h q ih =>
      rw [walkParity_cons, SimpleGraph.Walk.edges_cons, List.countP_cons, ih]
      by_cases hm : s(u, v) ∈ D
      · rw [decide_eq_true hm]
        simp only [Bool.true_xor]
        rcases Nat.mod_two_eq_zero_or_one
            (q.edges.countP (fun e => decide (e ∈ D))) with hn | hn
        · have hs : (q.edges.countP (fun e => decide (e ∈ D)) + 1) % 2 = 1 := by
            omega
          simp [hn, hs]
        · have hs : (q.edges.countP (fun e => decide (e ∈ D)) + 1) % 2 = 0 := by
            omega
          simp [hn, hs]
      · rw [decide_eq_false hm]
        simp


theorem kwg_latticeWalk_count (P : PlanarZ2Subgraph) {x y : P.V}
    (p : P.G.Walk x y) (e : Sym2 P.V) :
    (kwg_latticeWalk P p).edges.count (Sym2.map P.emb e) = p.edges.count e := by
  rw [show (kwg_latticeWalk P p).edges =
    List.map (Sym2.map P.emb) p.edges by
      have h1 := SimpleGraph.Walk.edges_map
        (f := SimpleGraph.Hom.ofLE (imageGraph_le_lattice P))
        (p := p.map (kwg_imageHom P))
      have h2 := SimpleGraph.Walk.edges_map (f := kwg_imageHom P) (p := p)
      unfold kwg_latticeWalk SimpleGraph.Walk.mapLe
      exact h1.trans (by
        rw [h2, List.map_map]
        apply congrArg (fun f => List.map f p.edges)
        funext z
        induction z using Sym2.inductionOn with
        | _ a b => rfl)]
  exact List.count_map_of_injective p.edges (Sym2.map P.emb)
    (Sym2.map.injective P.emb.injective) e


end Ising
end StatMech
