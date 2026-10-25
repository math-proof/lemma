/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part36
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem mem_doubledBoxOriginIncidentEdges
    {n : ℕ} {e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset} :
    e ∈ doubledBoxOriginIncidentEdges n ↔
      IsingFK.boxOrigin 3 (2 * n) ∈ e.1 := by
  classical
  simp [doubledBoxOriginIncidentEdges]

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentEdge_ne_of_origin_not_mem
    {n : ℕ}
    {e0 ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (he0origin : IsingFK.boxOrigin 3 (2 * n) ∉ e0.1)
    (hew : ew ∈ doubledBoxOriginIncidentEdges n) :
    ew ≠ e0 := by
  intro h
  exact he0origin
    (by
      simpa [h] using
        (mem_doubledBoxOriginIncidentEdges (n := n) (e := ew)).1 hew)

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentEdges_card_le_six (n : ℕ) :
    (doubledBoxOriginIncidentEdges n).card ≤ 6 := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let o := IsingFK.boxOrigin 3 (2 * n)
  have hcard :
      (doubledBoxOriginIncidentEdges n).card ≤
        (G.incidenceFinset o).card := by
    refine
      Finset.card_le_card_of_injOn
        (fun e => (e : Sym2 (FK.boxVerts 3 (2 * n)))) ?_ ?_
    · intro e he
      change (e : Sym2 (FK.boxVerts 3 (2 * n))) ∈ G.incidenceFinset o
      rw [SimpleGraph.mem_incidenceFinset]
      constructor
      · have heEdgeFinset :
            (e : Sym2 (FK.boxVerts 3 (2 * n))) ∈ G.edgeFinset := by
          change (e : Sym2 (FK.boxVerts 3 (2 * n))) ∈
            (FK.boxGraph 3 (2 * n)).edgeFinset
          exact e.2
        exact (SimpleGraph.mem_edgeFinset (G := G)).1 heEdgeFinset
      · exact (mem_doubledBoxOriginIncidentEdges (n := n)).1 he
    · intro a _ha b _hb hab
      exact Subtype.ext hab
  have hdegree :
      (G.incidenceFinset o).card = G.degree o := by
    exact SimpleGraph.card_incidenceFinset_eq_degree G o
  have hdeg_le : G.degree o ≤ 6 := by
    simpa [G] using StatMech.FK.qp_boxGraph_degree_le 3 (2 * n) o
  exact hcard.trans (by simpa [hdegree] using hdeg_le)

set_option linter.style.longLine false in


theorem candMap_origin_mem_doubledBox3_of_pos
    {n : ℕ} (hn : 0 < n) (p : Fin 3 × Bool) :
    Lattice.candMap 3 (0 : Lattice.Site 3) p ∈ Lattice.box 3 (2 * n) := by
  intro i
  by_cases hi : i = p.1
  · subst i
    rcases p with ⟨j, b⟩
    cases b <;> simp [Lattice.candMap, Lattice.shift] <;> omega
  · rcases p with ⟨j, b⟩
    simp [Lattice.candMap, Lattice.shift, Function.update_of_ne hi]

set_option linter.style.longLine false in


theorem six_le_doubledBoxOrigin_degree_of_pos
    {n : ℕ} (hn : 0 < n) :
    6 ≤ (FK.boxGraph 3 (2 * n)).degree (IsingFK.boxOrigin 3 (2 * n)) := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let o := IsingFK.boxOrigin 3 (2 * n)
  let nbr : Fin 3 × Bool → FK.boxVerts 3 (2 * n) :=
    fun p => ⟨Lattice.candMap 3 (0 : Lattice.Site 3) p,
      candMap_origin_mem_doubledBox3_of_pos (n := n) hn p⟩
  have hnbr_inj : Function.Injective nbr := by
    intro p q hpq
    exact Lattice.candMap_injective 3 (0 : Lattice.Site 3)
      (congrArg (fun x : FK.boxVerts 3 (2 * n) => (x : Lattice.Site 3)) hpq)
  have hsubset :
      (Finset.univ.image nbr) ⊆ G.neighborFinset o := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨p, _hp, rfl⟩
    rw [SimpleGraph.mem_neighborFinset]
    change
      (Lattice.hypercubicLattice 3).Adj
        ((o : FK.boxVerts 3 (2 * n)) : Lattice.Site 3)
        ((nbr p : FK.boxVerts 3 (2 * n)) : Lattice.Site 3)
    simpa [o, nbr, IsingFK.boxOrigin, Percolation.origin] using
      Lattice.adj_candMap 3 (0 : Lattice.Site 3) p
  have hcard : (Finset.univ.image nbr).card = 6 := by
    rw [Finset.card_image_of_injective _ hnbr_inj]
    simp [Fintype.card_prod]
  calc
    6 = (Finset.univ.image nbr).card := hcard.symm
    _ ≤ (G.neighborFinset o).card := Finset.card_le_card hsubset
    _ = G.degree o := G.card_neighborFinset_eq_degree o

set_option linter.style.longLine false in


theorem doubledBoxOrigin_degree_eq_six_of_pos
    {n : ℕ} (hn : 0 < n) :
    (FK.boxGraph 3 (2 * n)).degree (IsingFK.boxOrigin 3 (2 * n)) = 6 := by
  apply le_antisymm
  · simpa using
      StatMech.FK.qp_boxGraph_degree_le 3 (2 * n)
        (IsingFK.boxOrigin 3 (2 * n))
  · exact six_le_doubledBoxOrigin_degree_of_pos (n := n) hn

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentEdges_card_eq_degree (n : ℕ) :
    (doubledBoxOriginIncidentEdges n).card =
      (FK.boxGraph 3 (2 * n)).degree (IsingFK.boxOrigin 3 (2 * n)) := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let o := IsingFK.boxOrigin 3 (2 * n)
  have htoIncidence :
      (doubledBoxOriginIncidentEdges n).card ≤
        (G.incidenceFinset o).card := by
    refine
      Finset.card_le_card_of_injOn
        (fun e => (e : Sym2 (FK.boxVerts 3 (2 * n)))) ?_ ?_
    · intro e he
      change (e : Sym2 (FK.boxVerts 3 (2 * n))) ∈ G.incidenceFinset o
      rw [SimpleGraph.mem_incidenceFinset]
      constructor
      · have heEdgeFinset :
            (e : Sym2 (FK.boxVerts 3 (2 * n))) ∈ G.edgeFinset := by
          exact e.2
        exact (SimpleGraph.mem_edgeFinset (G := G)).1 heEdgeFinset
      · exact (mem_doubledBoxOriginIncidentEdges (n := n)).1 he
    · intro a _ha b _hb hab
      exact Subtype.ext hab
  have hfromIncidenceAttach :
      (G.incidenceFinset o).attach.card ≤
        (doubledBoxOriginIncidentEdges n).card := by
    refine
      Finset.card_le_card_of_injOn
        (fun e : {x // x ∈ G.incidenceFinset o} =>
          (⟨e.1, by
            have hinc := e.2
            rw [SimpleGraph.mem_incidenceFinset] at hinc
            exact (SimpleGraph.mem_edgeFinset (G := G)).2 hinc.1⟩ :
            ↥G.edgeFinset)) ?_ ?_
    · intro e _he
      change
        (⟨e.1, by
          have hinc := e.2
          rw [SimpleGraph.mem_incidenceFinset] at hinc
          exact (SimpleGraph.mem_edgeFinset (G := G)).2 hinc.1⟩ :
          ↥G.edgeFinset) ∈ doubledBoxOriginIncidentEdges n
      rw [mem_doubledBoxOriginIncidentEdges]
      have hinc := e.2
      rw [SimpleGraph.mem_incidenceFinset] at hinc
      exact hinc.2
    · intro a _ha b _hb hab
      apply Subtype.ext
      exact congrArg
        (fun e : ↥G.edgeFinset => (e : Sym2 (FK.boxVerts 3 (2 * n))))
        hab
  have hfromIncidence :
      (G.incidenceFinset o).card ≤
        (doubledBoxOriginIncidentEdges n).card := by
    simpa using hfromIncidenceAttach
  have hcard :
      (doubledBoxOriginIncidentEdges n).card =
        (G.incidenceFinset o).card :=
    le_antisymm htoIncidence hfromIncidence
  rw [hcard]
  change (G.incidenceFinset o).card = G.degree o
  exact SimpleGraph.card_incidenceFinset_eq_degree G o

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentEdges_card_eq_six_of_pos
    {n : ℕ} (hn : 0 < n) :
    (doubledBoxOriginIncidentEdges n).card = 6 := by
  rw [doubledBoxOriginIncidentEdges_card_eq_degree,
    doubledBoxOrigin_degree_eq_six_of_pos hn]

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentEdges_sum_le_of_forall_le_div_six
    {n : ℕ} (hn : 0 < n)
    {F : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℝ} {target : ℝ}
    (hF :
      ∀ e ∈ doubledBoxOriginIncidentEdges n, F e ≤ target / 6) :
    (∑ e ∈ doubledBoxOriginIncidentEdges n, F e) ≤ target := by
  classical
  calc
    (∑ e ∈ doubledBoxOriginIncidentEdges n, F e)
        ≤ ∑ e ∈ doubledBoxOriginIncidentEdges n, target / 6 :=
      Finset.sum_le_sum hF
    _ = target := by
      rw [Finset.sum_const, doubledBoxOriginIncidentEdges_card_eq_six_of_pos hn]
      norm_num
      ring

end Exact3D
end StatMech
