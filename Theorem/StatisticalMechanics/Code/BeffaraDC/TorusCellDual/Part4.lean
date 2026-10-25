/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusDefectComplement.Part2
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellDual.Part4
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager


theorem torusCellDualOfPrimalEdge_of_mem (L : ℕ) [Fact (2 < L)]
    {e : Sym2 (ZMod L × ZMod L)}
    (he : e ∈ (onsTorusGraph L).edgeFinset) :
    torusCellDualOfPrimalEdge L e =
      (torusCellCrossing L ⟨e, he⟩ : TorusAmbientEdge L) := by
  simp [torusCellDualOfPrimalEdge, he]


theorem torusCellDualCutGraph_sup_edge (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) {p q : ZMod L × ZMod L}
    (hpq : (onsTorusGraph L).Adj p q) :
    torusCellDualCutGraph L (G ⊔ edge p q) =
      (torusCellDualCutGraph L G).deleteEdges
        {torusCellDualOfPrimalEdge L s(p, q)} := by
  let ep : TorusAmbientEdge L :=
    ⟨s(p, q), by simpa only [SimpleGraph.mem_edgeFinset] using hpq⟩
  let ed : TorusAmbientEdge L := torusCellCrossing L ep
  have hed : torusCellDualOfPrimalEdge L s(p, q) =
      (ed : Sym2 (ZMod L × ZMod L)) := by
    simpa [ed] using torusCellDualOfPrimalEdge_of_mem L ep.2
  ext f g
  by_cases hfg : (onsTorusGraph L).Adj f g
  · have hefg : s(f, g) ∈ (onsTorusGraph L).edgeFinset := by
      simpa only [SimpleGraph.mem_edgeFinset] using hfg
    have hcross : torusCellPrimalOfDualEdge L s(f, g) = s(p, q) ↔
        s(f, g) = (ed : Sym2 (ZMod L × ZMod L)) := by
      rw [torusCellPrimalOfDualEdge_of_mem L hefg]
      constructor
      · intro h
        have hs : (torusCellCrossing L).symm
            (⟨s(f, g), hefg⟩ : TorusAmbientEdge L) = ep :=
          Subtype.ext h
        have := congrArg (torusCellCrossing L) hs
        simpa [ed] using congrArg Subtype.val this
      · intro h
        have hs : (⟨s(f, g), hefg⟩ : TorusAmbientEdge L) = ed :=
          Subtype.ext h
        have := congrArg (torusCellCrossing L).symm hs
        simpa [ep, ed] using congrArg Subtype.val this
    simp only [torusCellDualCutGraph_adj, deleteEdges_adj, hfg, true_and,
      Set.mem_singleton_iff]
    rw [hed]
    rw [edgeSet_sup, edgeSet_edge_of_ne hpq.ne]
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or]
    exact and_congr_right (fun _ => not_congr hcross)
  · simp [torusCellDualCutGraph_adj, deleteEdges_adj, hfg]


end StatMech.BeffaraDC
