/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron.Part8


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem sixVertexCanonicalHalfDensityFloor_pos
    {c : Real} (hc : 2 < c) :
    0 < sixVertexCanonicalHalfDensityFloor hc :=
  (Classical.choose_spec
    (eventually_sixVertexCanonicalDensityPerronFiniteDensity_lower hc)).1

theorem eventually_sixVertexCanonicalHalfDensityFloor_le
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop, forall x,
      sixVertexCanonicalHalfDensityFloor hc <=
        sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1))
          (sixVertexCanonicalDensityPerronBetheRoots hc k) x :=
  (Classical.choose_spec
    (eventually_sixVertexCanonicalDensityPerronFiniteDensity_lower hc)).2

end
end StatMech.FrontierD
