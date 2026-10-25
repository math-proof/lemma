/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectInducedConditionalLower.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalFullGraphLaw.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreConditionalLowerProduct
import Def.StatisticalMechanics.Code.FrontierD.FKRectInducedConditionalLower.Part3
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectFullGraphEvent_mass_eq
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (B : Set R.Configuration) :
    (∑ rho : ConfigSpace (Sym2 R.Vertex),
        (fkRectFullGraphEvent R B).indicator (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R) (fkRectCriticalP q) q rho) =
      fkRectCriticalEventMass R q B := by
  exact (fkRectCriticalEventMass_eq_fullGraph R hq B).symm


end
end StatMech.FrontierD
