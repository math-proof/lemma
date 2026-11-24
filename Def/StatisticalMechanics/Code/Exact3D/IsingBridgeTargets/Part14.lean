module
public import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
public import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
public import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part13


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

noncomputable def freeSelectedSubcriticalMass
    (h : FreeSubcriticalMassBridge) (β : ℝ) : ℝ :=
  if hβ : β < Ising.betaC 3 then Classical.choose (h β hβ) else 0


end Exact3D
end StatMech
