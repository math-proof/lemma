/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part75
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_axisGapFiniteGraph {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y :=
    (hypercubicLattice 2).Adj (x : Site 2) (y : Site 2) ∧
      s((x : Site 2), (y : Site 2)) ∈ rlc_axisGapEdges G
  symm := by
    constructor
    intro x y hxy
    exact ⟨hxy.1.symm, by simpa [Sym2.eq_swap] using hxy.2⟩
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

end
end StatMech.Universality
