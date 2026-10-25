/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeEndpoint


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Filter Topology

noncomputable section

def oddPrismUpperHalfSurfaceSite (n : Nat) (hn : 0 < n)
    (i j : Fin (2 * n + 1)) : OddPrismUpperBlockSite n :=
  ⟨⟨i, j, ⟨n + 1, by omega⟩⟩, by
    unfold oddPrismAtOrBelowCenter
    simp only
    omega⟩


def oddPrismCentralInterfaceEdge (n : Nat) (hn : 0 < n)
    (i j : Fin (2 * n + 1)) :
    Sym2 (OddPrismLowerBlockSite n ⊕ OddPrismUpperBlockSite n) :=
  s(Sum.inl (oddPrismLowerHalfSurfaceSite n i j),
    Sum.inr (oddPrismUpperHalfSurfaceSite n hn i j))


end
end StatMech.FrontierA
