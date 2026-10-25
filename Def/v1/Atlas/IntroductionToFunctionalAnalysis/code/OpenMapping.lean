/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/OpenMapping.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Operator.Banach


namespace OpenMapping

open Function

/-- The continuous linear equivalence $V \simeq_L W$ constructed from a bijective bounded
linear operator $T : V \to W$ between Banach spaces. By the Open Mapping Theorem, the
set-theoretic inverse is automatically continuous, so $T$ upgrades to a continuous linear
equivalence. -/
noncomputable def continuousLinearEquivOfBijective
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]
    (T : V →L[𝕜] W) (hT : Bijective T) : V ≃L[𝕜] W :=
  ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr hT.1)
    (LinearMap.range_eq_top.mpr hT.2)

end OpenMapping
