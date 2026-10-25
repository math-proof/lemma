/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part7


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


namespace finiteCRSFCycleSupport

noncomputable def toFiber {next : V -> V}
    (S : finiteCRSFCycleSupport next) : finiteCRSFWitnessFiber next :=
  ⟨S.toWitness, S.next_toWitness⟩


noncomputable def term {next : V -> V}
    (conductance transport : V -> V -> Complex)
    (S : finiteCRSFCycleSupport next) : Complex :=
  Equiv.Perm.sign S.ambientPerm •
    ((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
        conductance v (next v)) *
      ∏ v ∈ S.carrier,
        -conductance v (next v) * transport v (next v))


end finiteCRSFCycleSupport
end StatMech.FrontierA
