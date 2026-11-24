module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part6
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem eventually_exists_sixVertexCanonicalFixedOddDensityWitness
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      ∃ p, SixVertexCanonicalFixedOddDensityWitness hc s k p :=
  (Classical.choose_spec
    (eventually_exists_sixVertexFixedOddChargeBethePerronBranch_with_densityFloor
      hc s)).2

end
end StatMech.FrontierD
