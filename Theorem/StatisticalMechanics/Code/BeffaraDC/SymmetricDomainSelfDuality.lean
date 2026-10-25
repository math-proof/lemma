/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part3
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

@[simp] theorem onGammaOne_gammaOneStart (D : SymmetricDomain) :
    D.OnGammaOne D.gammaOneStart := by
  exact D.γ₁.start_mem_support

@[simp] theorem onGammaTwo_gammaTwoStart (D : SymmetricDomain) :
    D.OnGammaTwo D.gammaTwoStart := by
  exact D.γ₂.start_mem_support


end SymmetricDomain
end
end BeffaraDC
end StatMech
