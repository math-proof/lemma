/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GeneralTrifurcationPattern.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.InfiniteClusterTail.Part3
import Theorem.StatisticalMechanics.Code.Percolation.LatticeThreeExitTree.Part2
import Theorem.StatisticalMechanics.Code.Percolation.TreeExteriorAmalgam
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.OutwardArmForestClose.Part3
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Percolation

variable {d : ℕ}


noncomputable def programmedTreeEdges {W : Type*} [Fintype W]
    (T : SimpleGraph W) [DecidableRel T.Adj] (f : W → Site d) :
    Finset (Sym2 (Site d)) := T.edgeFinset.image (Sym2.map f)


noncomputable def programmedTreePattern (I O : Finset (Sym2 (Site d))) :
    ConfigSpace ↥I := fun e => decide (e.1 ∈ O)


def exteriorOpenGraph (omega : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    SimpleGraph (Site d) where
  Adj x y := (openSubgraph d omega).Adj x y ∧ x ∉ box d n ∧ y ∉ box d n
  symm := by constructor; rintro x y ⟨h, hx, hy⟩; exact ⟨h.symm, hy, hx⟩
  loopless := ⟨fun _ h => (openSubgraph d omega).irrefl h.1⟩

end StatMech.Percolation
