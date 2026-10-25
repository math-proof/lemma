/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCut
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlus.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Abbrev.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

def ons_plusWiredVertexOfSite (d n : Nat) (x : Site d) :
    ons_PlusWiredVertex d n :=
  if hx : x ∈ box d n then some ⟨x, hx⟩ else none


def ons_plusWiredBondEnds (d n : Nat) (edge : ons_PlusWiredBond d n) :
    ons_PlusWiredVertex d n × ons_PlusWiredVertex d n :=
  (ons_plusWiredVertexOfSite d n edge.1.out.1,
    ons_plusWiredVertexOfSite d n edge.1.out.2)


end
end StatMech.Onsager
