/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeanePattern.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTail.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ThreePendantTree
import Theorem.StatisticalMechanics.Code.Percolation.TreeExteriorAmalgam
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeanePattern
open MeasureTheory Set SimpleGraph Finset


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type} [Countable V] [DecidableEq V]

noncomputable def programmedPeriodicTreeEdges {W : Type*} [Fintype W]
    (T : SimpleGraph W) [DecidableRel T.Adj] (f : W → V) :
    Finset (Sym2 V) := T.edgeFinset.image (Sym2.map f)

noncomputable def programmedPeriodicTreePattern (I O : Finset (Sym2 V)) :
    ConfigSpace ↥I := fun e => decide (e.1 ∈ O)

def PeriodicGraph.exteriorOpenGraph (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (K : Finset V) : SimpleGraph V where
  Adj x y := (P.openSubgraph omega).Adj x y ∧ x ∉ K ∧ y ∉ K
  symm := by constructor; rintro x y ⟨h, hx, hy⟩; exact ⟨h.symm, hy, hx⟩
  loopless := ⟨fun _ h => (P.openSubgraph omega).irrefl h.1⟩

end StatMech.FK.PeriodicPlanar
