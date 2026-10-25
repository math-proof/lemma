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
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part19
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


theorem kwg_cutEdges_eq_of_nonempty_subset_of_colourSidesConnected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c d : V → Bool)
    (hcconn : kwg_ColourSidesConnected G c)
    (hsub : cutEdges G d ⊆ cutEdges G c)
    (hne : (cutEdges G d).Nonempty) :
    cutEdges G d = cutEdges G c := by
  classical
  have sideConst : ∀ {a b : V}, c a = c b → d a = d b := by
    intro a b hab
    obtain ⟨w⟩ := hcconn (c a) ⟨a, rfl⟩ ⟨b, hab.symm⟩
    let wG : G.Walk a b :=
      w.map (SimpleGraph.Embedding.induce {v : V | c v = c a}).toHom
    have hwG : ∀ z ∈ wG.support, c z = c a := by
      intro z hz
      change z ∈
        (w.map (SimpleGraph.Embedding.induce {v : V | c v = c a}).toHom).support at hz
      rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
      exact z'.2
    have propagate : ∀ {q r : V} (p : G.Walk q r),
        (∀ z ∈ p.support, c z = c q) → d q = d r := by
      intro q r p hp
      induction p with
      | nil => rfl
      | @cons x y z hxy p ih =>
          have hcxy : c x = c y := (hp x (by simp)).trans (hp y (by simp)).symm
          have hnotc : s(x, y) ∉ cutEdges G c := by
            rw [mem_cutEdges_iff G c hxy]
            exact fun hne => hne hcxy
          have hnotd : s(x, y) ∉ cutEdges G d := fun hd => hnotc (hsub hd)
          have hdxy : d x = d y := by
            by_contra hne
            exact hnotd ((mem_cutEdges_iff G d hxy).mpr hne)
          exact hdxy.trans (ih (fun z hz => (hp z (by simp [hz])).trans hcxy))
    exact propagate wG hwG
  obtain ⟨e, he⟩ := hne
  have heG : e ∈ G.edgeFinset := Finset.filter_subset _ _ he
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : G.Adj x y := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at heG
      have hdxy : d x ≠ d y := (mem_cutEdges_iff G d hxy).mp he
      have hcxy : c x ≠ c y := (mem_cutEdges_iff G c hxy).mp (hsub he)
      apply Finset.ext
      intro f
      induction f using Sym2.inductionOn with
      | _ a b =>
          by_cases habG : G.Adj a b
          · rw [mem_cutEdges_iff G d habG, mem_cutEdges_iff G c habG]
            constructor
            · intro hdab hcab
              exact hdab (sideConst hcab)
            · intro hcab hdab
              have haxay : c a = c x ∨ c a = c y := by
                cases ha : c a <;> cases hx : c x <;> cases hy : c y <;> simp_all
              have hbxby : c b = c x ∨ c b = c y := by
                cases hb : c b <;> cases hx : c x <;> cases hy : c y <;> simp_all
              rcases haxay with hax | hay <;> rcases hbxby with hbx | hby
              · exact hcab (hax.trans hbx.symm)
              · exact hdxy ((sideConst hax).symm.trans (hdab.trans (sideConst hby)))
              · exact hdxy ((sideConst hbx).symm.trans (hdab.symm.trans (sideConst hay)))
              · exact hcab (hay.trans hby.symm)
          · have hnd : s(a, b) ∉ cutEdges G d := by
              intro h
              exact habG (SimpleGraph.mem_edgeFinset.mp ((Finset.filter_subset _ _) h))
            have hnc : s(a, b) ∉ cutEdges G c := by
              intro h
              exact habG (SimpleGraph.mem_edgeFinset.mp ((Finset.filter_subset _ _) h))
            simp [hnd, hnc]


theorem kwg_dualEven_subset_bond_eq (P : PlanarZ2Subgraph) (c : ConfigSpace P.V)
    (hcconn : kwg_ColourSidesConnected P.G c)
    (F : Finset (kwg_Edge P))
    (hsub : F ⊆ kwg_cutSet (kwg_primalEnds P) c) (hne : F.Nonempty)
    (heven : kwg_IsEven (kwg_dualEnds P) F) :
    F = kwg_cutSet (kwg_primalEnds P) c := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  obtain ⟨d, hd⟩ := (kwg_geometricCutCycleDuality P F).mp heven
  have hsub' : kwg_cutSet (kwg_primalEnds P) d ⊆
      kwg_cutSet (kwg_primalEnds P) c := by
    rw [hd]
    exact hsub
  have hcutSub : cutEdges P.G d ⊆ cutEdges P.G c := by
    rw [← kwg_primalEdgeFinset_cutSet P d, ← kwg_primalEdgeFinset_cutSet P c]
    exact Finset.map_subset_map.mpr hsub'
  have hcutNe : (cutEdges P.G d).Nonempty := by
    rw [← kwg_primalEdgeFinset_cutSet P d, hd]
    exact Finset.map_nonempty.mpr hne
  have hcutEq := kwg_cutEdges_eq_of_nonempty_subset_of_colourSidesConnected
    P.G c d hcconn hcutSub hcutNe
  have hindexEq : kwg_cutSet (kwg_primalEnds P) d =
      kwg_cutSet (kwg_primalEnds P) c :=
    (kwg_cutSet_eq_iff_cutEdges_eq P d c).mpr hcutEq
  rw [← hd, hindexEq]


end Ising
end StatMech
