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
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

def ons_plusWiredPathNumerator
    (d n : Nat) (beta : Real) (u v : Site d) : Real :=
  ∑ config : AnchoredConfig (ons_PlusWiredVertex d n) none,
    ons_plusWiredEndpointSign d n config.1 u v *
      Real.exp (-2 * beta) ^
        (multibondCut (ons_plusWiredBondEnds d n) config.1).card


end
end StatMech.Onsager
