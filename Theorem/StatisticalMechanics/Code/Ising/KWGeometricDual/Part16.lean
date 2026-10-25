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
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part17
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


theorem kwg_componentTwist_cutEdges (P : PlanarZ2Subgraph) (c : ConfigSpace P.V)
    (a : P.G.ConnectedComponent → Bool) :
    cutEdges P.G (kwg_componentTwist P c a) = cutEdges P.G c := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      by_cases hxy : P.G.Adj x y
      · rw [mem_cutEdges_iff P.G _ hxy, mem_cutEdges_iff P.G _ hxy]
        have hcomp : P.G.connectedComponentMk x = P.G.connectedComponentMk y :=
          ConnectedComponent.sound hxy.reachable
        simp only [kwg_componentTwist, hcomp]
        cases a (P.G.connectedComponentMk y) <;> cases c x <;> cases c y <;> simp
      · have hn1 : s(x, y) ∉ cutEdges P.G (kwg_componentTwist P c a) := by
          intro h
          have hedge := (Finset.filter_subset _ _) h
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hedge
          exact hxy hedge
        have hn2 : s(x, y) ∉ cutEdges P.G c := by
          intro h
          have hedge := (Finset.filter_subset _ _) h
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hedge
          exact hxy hedge
        simp [hn1, hn2]


theorem kwg_primalCut_fiber_card (P : PlanarZ2Subgraph) (c : ConfigSpace P.V) :
    (Finset.univ.filter (fun d : ConfigSpace P.V =>
      kwg_cutSet (kwg_primalEnds P) d = kwg_cutSet (kwg_primalEnds P) c)).card =
        2 ^ Nat.card P.G.ConnectedComponent := by
  classical
  let mapFiber : ConfigSpace P.V → (P.G.ConnectedComponent → Bool) :=
    fun d C => decide (c C.out = d C.out)
  have hcard := Finset.card_bij
    (fun d (_ : d ∈ Finset.univ.filter (fun d : ConfigSpace P.V =>
      kwg_cutSet (kwg_primalEnds P) d = kwg_cutSet (kwg_primalEnds P) c)) => mapFiber d)
    (s := Finset.univ.filter (fun d : ConfigSpace P.V =>
      kwg_cutSet (kwg_primalEnds P) d = kwg_cutSet (kwg_primalEnds P) c))
    (t := (Finset.univ : Finset (P.G.ConnectedComponent → Bool)))
    (by simp)
    (by
      intro d hd e he hmap
      apply funext
      intro v
      have hdcut : cutEdges P.G d = cutEdges P.G c :=
        (kwg_cutSet_eq_iff_cutEdges_eq P d c).mp (Finset.mem_filter.mp hd).2
      have hecut : cutEdges P.G e = cutEdges P.G c :=
        (kwg_cutSet_eq_iff_cutEdges_eq P e c).mp (Finset.mem_filter.mp he).2
      let q := kwg_componentPath P.G v
      have hdprop := agree_walk P.G hdcut.symm q
      have heprop := agree_walk P.G hecut.symm q
      have hroot : (c (P.G.connectedComponentMk v).out = d (P.G.connectedComponentMk v).out) ↔
          (c (P.G.connectedComponentMk v).out = e (P.G.connectedComponentMk v).out) :=
        decide_eq_decide.mp (congrFun hmap (P.G.connectedComponentMk v))
      have hv : (c v = d v) ↔ (c v = e v) :=
        hdprop.symm.trans (hroot.trans heprop)
      cases hc : c v <;> cases hdv : d v <;> cases hev : e v <;> simp_all)
    (by
      intro a _
      let d := kwg_componentTwist P c a
      have hdcut : kwg_cutSet (kwg_primalEnds P) d = kwg_cutSet (kwg_primalEnds P) c :=
        (kwg_cutSet_eq_iff_cutEdges_eq P d c).mpr (kwg_componentTwist_cutEdges P c a)
      refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdcut⟩, ?_⟩
      funext C
      have hC : P.G.connectedComponentMk C.out = C := C.out_eq
      simp only [mapFiber, d, kwg_componentTwist, hC]
      cases a C <;> cases c C.out <;> simp)
  rw [hcard, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    ← Nat.card_eq_fintype_card]


theorem kwg_primalCut_sum (P : PlanarZ2Subgraph) (t : ℝ) : by
    letI : Fintype P.V := Fintype.ofFinite P.V
    exact (∑ c : ConfigSpace P.V, t ^ (kwg_cutSet (kwg_primalEnds P) c).card) =
      ∑ c : ConfigSpace P.V, t ^ (cutEdges P.G c).card := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  apply Finset.sum_congr rfl
  intro c _
  rw [kwg_primalCut_card P c]


end Ising
end StatMech
