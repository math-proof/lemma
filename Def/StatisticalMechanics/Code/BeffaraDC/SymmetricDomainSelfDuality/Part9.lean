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
import Structure.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

noncomputable def MixedDualComplementRN.disconnectedEquivConnected
    {D : SymmetricDomain} {q : Real} (R : MixedDualComplementRN D q) :
    {omega : ConfigSpace (Sym2 D.Vertex) // ¬D.MixedConnected omega} ≃
      {eta : ConfigSpace (Sym2 D.Vertex) // D.MixedConnected eta} where
  toFun omega := ⟨R.dual omega.1,
    (R.connected_dual_iff omega.1).mpr omega.2⟩
  invFun eta := ⟨R.dual.symm eta.1, by
    apply (R.connected_dual_iff (R.dual.symm eta.1)).mp
    simpa using eta.2⟩
  left_inv omega := by
    apply Subtype.ext
    exact R.dual.symm_apply_apply omega.1
  right_inv eta := by
    apply Subtype.ext
    exact R.dual.apply_symm_apply eta.1


end SymmetricDomain
end
end BeffaraDC
end StatMech
