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
import Def.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part9
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

theorem MixedDualComplementRN.card_disconnected_eq_card_connected
    {D : SymmetricDomain} {q : Real} (R : MixedDualComplementRN D q) :
    Fintype.card
        {omega : ConfigSpace (Sym2 D.Vertex) // ¬D.MixedConnected omega} =
      Fintype.card
        {eta : ConfigSpace (Sym2 D.Vertex) // D.MixedConnected eta} :=
  Fintype.card_congr R.disconnectedEquivConnected


theorem MixedDualComplementRN.exists_connected_and_disconnected
    {D : SymmetricDomain} {q : Real} (R : MixedDualComplementRN D q) :
    (∃ omega, D.MixedConnected omega) ∧
      ∃ eta, ¬D.MixedConnected eta := by
  let omega : ConfigSpace (Sym2 D.Vertex) := fun _ => false
  by_cases hconnected : D.MixedConnected omega
  · refine ⟨⟨omega, hconnected⟩, ?_⟩
    let eta := R.dual.symm omega
    refine ⟨eta, ?_⟩
    apply (R.connected_dual_iff eta).mp
    simpa [eta] using hconnected
  · exact ⟨⟨R.dual omega,
      (R.connected_dual_iff omega).mpr hconnected⟩, ⟨omega, hconnected⟩⟩


end SymmetricDomain
end
end BeffaraDC
end StatMech
