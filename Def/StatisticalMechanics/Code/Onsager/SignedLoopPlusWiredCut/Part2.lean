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
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

def ons_plusWiredCutLattice
    (d n : Nat) (tau : {x // x ∈ box d n} → Bool) :
    Finset (Sym2 (Site d)) :=
  (multibondCut (ons_plusWiredBondEnds d n)
    (ons_optionAnchoredEquiv tau).1).map
      ⟨Subtype.val, Subtype.val_injective⟩


end
end StatMech.Onsager
