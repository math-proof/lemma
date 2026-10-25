/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricAnalytic.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

structure SixVertexLocalAnalyticOddSymmetricBetheBranch
    (N m : Nat) (c : Real) (q : Fin m → Real) where
  roots : Real → (Fin m → Real)
  analyticAt_roots : AnalyticAt Real roots c
  roots_at : roots c = q
  eventually_solution : ∀ᶠ t in nhds c,
    SixVertexSatisfiesBetheEquations t N ((m + 1) + m)
      (sixVertexOddSymmetricLift m (roots t))
  eventually_unique : ∀ᶠ z : Real × (Fin m → Real) in nhds (c, q),
    SixVertexSatisfiesBetheEquations z.1 N ((m + 1) + m)
      (sixVertexOddSymmetricLift m z.2) → roots z.1 = z.2

end
end StatMech.FrontierD
