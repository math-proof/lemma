/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part7
open Finset Matrix


namespace StatMech.FrontierD

noncomputable def svFinitePeriodicSuccEquiv {N : Nat} (hN : 0 < N) :
    Fin N ≃ Fin N :=
  Equiv.ofBijective (finitePeriodicSucc hN)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨svFinitePeriodicSucc_injective hN, rfl⟩)

end StatMech.FrontierD
