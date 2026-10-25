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
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

def ons_plusWiredEndpointSign
    (d n : Nat) (config : ConfigSpace (ons_PlusWiredVertex d n))
    (u v : Site d) : Real :=
  spin config (ons_plusWiredVertexOfSite d n u) *
    spin config (ons_plusWiredVertexOfSite d n v)


end
end StatMech.Onsager
