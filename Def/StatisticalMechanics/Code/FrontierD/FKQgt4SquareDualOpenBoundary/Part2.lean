/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualOpenBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualCoverageGeometry
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareBoxClusterUnion
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualOpenBoundary
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.FK.PeriodicPlanar

noncomputable section

noncomputable def squareDualClusterCoverage_boundaryHom
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    (hfinite : ∀ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Finite) :
    let S := squareDualClusterCoverage omega n
    let hS := squareDualClusterCoverage_finite omega n hfinite
    faceBoundaryGraph (squareHoleFill S hS) →g openSubgraph 2 omega := by
  dsimp only
  let S := squareDualClusterCoverage omega n
  let hS : S.Finite := squareDualClusterCoverage_finite omega n hfinite
  let K := squareHoleFill S hS
  have hKclosed : ∀ {x y}, x ∈ K →
      (fci_faceOpenDual omega).Adj x y → y ∈ K :=
    squareHoleFill_closed_of_faceDual_closed omega S hS
      (squareDualClusterCoverage_closed omega n)
  refine
    { toFun := square.shift squareDualBoundaryShift
      map_rel' := ?_ }
  intro f g hfg
  have hlat : (hypercubicLattice 2).Adj
      (square.shift squareDualBoundaryShift f)
      (square.shift squareDualBoundaryShift g) :=
    (square.shift_adj squareDualBoundaryShift f g).2 hfg.1
  refine ⟨hlat, ?_⟩
  have hedge : symPrimalSym s(f, g) ∈ boundaryEdgeSet K :=
    symPrimalSym_mem_boundaryEdgeSet
      ((SimpleGraph.mem_edgeSet _).2 hfg)
  have hinverse : flankFacesSym (symPrimal f g) = s(f, g) :=
    flankFacesSym_symPrimal hfg.1
  rw [symPrimalSym_mk] at hedge
  generalize heq : symPrimal f g = e at hedge hinverse
  induction e using Sym2.inductionOn with
  | _ p q =>
      rw [flankFacesSym_mk] at hinverse
      have hpq : (hypercubicLattice 2).Adj p q :=
        (SimpleGraph.mem_edgeSet _).1 hedge.1
      have hopen := sharedPrimalEdge_open_of_faceDual_closed
        omega K hKclosed hpq hedge
      have hshift := squareDualBoundaryShift_flankFaces_eq_sharedPrimalEdge hpq
      rw [hinverse, Sym2.map_mk] at hshift
      rwa [hshift]

end
end StatMech.FrontierD
