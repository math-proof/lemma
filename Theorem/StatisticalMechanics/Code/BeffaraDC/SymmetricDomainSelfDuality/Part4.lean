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
import Def.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part8
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

theorem mixedConnection_add_disconnection_eq_one
    (D : SymmetricDomain) {q : Real} (hq : 1 ≤ q) :
    D.mixedConnectionProbability q + D.mixedDisconnectionProbability q = 1 := by
  have hq0 : 0 < q := one_pos.trans_le hq
  obtain ⟨hp0, hp1⟩ := selfDualPoint_mem_Ioo hq0
  rw [mixedConnectionProbability, mixedDisconnectionProbability,
    ← Finset.sum_add_distrib]
  calc
    (∑ omega : ConfigSpace (Sym2 D.Vertex),
        ((if D.MixedConnected omega then D.mixedMass q omega else 0) +
          if ¬D.MixedConnected omega then D.mixedMass q omega else 0)) =
        ∑ omega : ConfigSpace (Sym2 D.Vertex), D.mixedMass q omega := by
          apply Finset.sum_congr rfl
          intro omega _
          by_cases hconn : D.MixedConnected omega <;> simp [hconn]
    _ = 1 := FK.bcProb_sum_eq_one D.finiteGraph D.mixedWiring hp0 hp1 hq0


end SymmetricDomain
end
end BeffaraDC
end StatMech
