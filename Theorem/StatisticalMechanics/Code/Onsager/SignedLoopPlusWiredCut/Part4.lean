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
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

theorem ons_plusWiredEndpointSign_eq_pathSign
    (d n : Nat) (tau : {x // x ∈ box d n} → Bool)
    {u v : Site d} (path : (hypercubicLattice d).Walk u v) :
    ons_plusWiredEndpointSign d n (ons_optionAnchoredEquiv tau).1 u v =
      ons_plusLowTempPathSign (glue (plusField d) tau) path := by
  rw [ons_plusLowTempPathSign_eq_spin_mul]
  unfold ons_plusWiredEndpointSign
  unfold spin
  rw [ons_optionAnchoredEquiv_apply_vertexOfSite,
    ons_optionAnchoredEquiv_apply_vertexOfSite]
  cases glue (plusField d) tau u <;>
    cases glue (plusField d) tau v <;> norm_num


end
end StatMech.Onsager
